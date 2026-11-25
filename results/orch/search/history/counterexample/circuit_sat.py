import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

class CNF:
    def __init__(self):
        self.n = 0
        self.rows = []
    def var(self):
        self.n += 1
        return self.n
    def clause(self, *ls):
        if any(x is True for x in ls): return
        xs = list(dict.fromkeys(x for x in ls if x is not False))
        if any(-x in xs for x in xs): return
        self.rows.append(xs)
    def one(self, xs):
        self.clause(*xs)
        # Sequential at-most-one encoding.
        prev = None
        for x in xs[:-1]:
            out = self.var()
            self.clause(-x, out)
            if prev is not None:
                self.clause(-prev, out)
                self.clause(-prev, -x)
            prev = out
        if prev is not None: self.clause(-prev, -xs[-1])
    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.rows)}\n')
            for r in self.rows: f.write(' '.join(map(str,r))+' 0\n')

def neg(x): return not x if isinstance(x,bool) else -x

def graph(name, cycle):
    if name == 'cycle':
        return cycle, [(i,(i+1)%cycle) for i in range(cycle)], [(0,j) for j in range(1,cycle//2+1)]
    if name in ('theta233','k4sub'):
        if name == 'theta233':
            n=7; edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
        else:
            n=8; edges=[(0,1),(2,3),(0,4),(4,2),(0,5),(5,3),(1,6),(6,2),(1,7),(7,3)]
        eset={tuple(sorted(e)) for e in edges}
        autos=[p for p in itertools.permutations(range(n)) if {tuple(sorted((p[i],p[j]))) for i,j in edges}==eset]
        pairs=[]; seen=set()
        for i,j in sorted(itertools.combinations(range(n),2),key=lambda p:(p[1],p[0])):
            if (i,j) not in seen:
                pairs.append((i,j)); seen.update(tuple(sorted((p[i],p[j]))) for p in autos)
        return n,edges,pairs
    vertices=list(itertools.combinations(range(5),2))
    return 10,[(i,j) for i,j in itertools.combinations(range(10),2) if not(set(vertices[i])&set(vertices[j]))],[(0,1),(2,4)]

def solve(args):
    n,edges,pairs=graph(args.graph,args.cycle); k=args.gates
    def target(x): return any((x>>i)&(x>>j)&1 for i,j in edges)
    positives=sorted({(1<<i)|(1<<j) for i,j in edges})
    negatives=[x for x in range(1<<n) if not target(x) and all(target(x|(1<<i)) for i in range(n) if not(x>>i&1))]
    tests=positives+negatives
    cnf=CNF()
    ops=[cnf.var() for _ in range(k)]
    sels=[[[cnf.var() for i in range(n+g)] for b in range(2)] for g in range(k)]
    vals=[[cnf.var() for _ in tests] for g in range(k)]
    operands=[[[cnf.var() for _ in tests] for b in range(2)] for g in range(k)]
    for g in range(k):
        for b in range(2):
            cnf.one(sels[g][b])
            for i,s in enumerate(sels[g][b]):
                for t,x in enumerate(tests):
                    v=bool(x>>i&1) if i<n else vals[i-n][t]
                    z=operands[g][b][t]
                    cnf.clause(-s,neg(v),z); cnf.clause(-s,v,-z)
        for i in range(n+g):
            for j in range(i+1):cnf.clause(-sels[g][0][i],-sels[g][1][j])
        for t,x in enumerate(tests):
            a,b=operands[g][0][t],operands[g][1][t]; z=vals[g][t]; op=ops[g]
            cnf.clause(op,-a,-b,z);cnf.clause(op,a,-z);cnf.clause(op,b,-z)
            cnf.clause(-op,a,b,-z);cnf.clause(-op,-a,z);cnf.clause(-op,-b,z)
    for i,j in itertools.combinations(range(n),2):
        if (i,j) not in pairs:cnf.clause(-sels[0][0][i],-sels[0][1][j])
    for g in range(k-1):cnf.clause(*(sels[h][b][n+g] for h in range(g+1,k) for b in range(2)))
    if args.ordered:
        for g in range(k-1):
            for i in range(n+g):
                for j in range(i):cnf.clause(-sels[g][1][i],-sels[g+1][1][j])
    for t,x in enumerate(tests):cnf.clause(vals[-1][t] if target(x) else -vals[-1][t])
    if args.dirty:
        dirty=[]
        for g in range(k):
            for t in range(len(positives),len(tests)):
                d=cnf.var();dirty.append(d)
                cnf.clause(-d,-ops[g]);cnf.clause(-d,vals[g][t])
        cnf.clause(*dirty)
    if args.honest:
        for g in range(k):
            for t in range(len(positives),len(tests)):cnf.clause(ops[g],-vals[g][t])
    base=Path(args.output)
    cnf.write(base.with_suffix('.cnf'))
    start=time.monotonic()
    with base.with_suffix('.solver.stdout').open('w') as out,base.with_suffix('.solver.stderr').open('w') as err:
        proc=subprocess.run([args.solver,'-t',str(args.seconds),str(base.with_suffix('.cnf'))],stdout=out,stderr=err)
    result={'graph':args.graph,'n':n,'edges':edges,'gates':k,'tests':len(tests),'variables':cnf.n,'clauses':len(cnf.rows),'seconds':time.monotonic()-start,'returncode':proc.returncode}
    if proc.returncode==10:
        assignment=set()
        for line in base.with_suffix('.solver.stdout').read_text().splitlines():
            if line.startswith('v '):assignment.update(int(s) for s in line[2:].split() if int(s)>0)
        circuit=[]
        for g in range(k):
            ij=[next(i for i,s in enumerate(sels[g][b]) if s in assignment) for b in range(2)]
            circuit.append([int(ops[g] in assignment),*ij])
        dirty=[]
        for g,(op,i,j) in enumerate(circuit):
            if op:continue
            false_inputs=[]; essential=[]
            for x in range(1<<n):
                w=[(x>>i)&1 for i in range(n)]
                for h,(o,a,b) in enumerate(circuit):w.append((w[a]|w[b]) if o else (w[a]&w[b]))
                assert bool(w[-1])==target(x)
                if w[n+g] and not target(x):false_inputs.append(x)
            if false_inputs:
                for x in positives:
                    w=[(x>>i)&1 for i in range(n)]
                    for h,(o,a,b) in enumerate(circuit):w.append(0 if h==g else ((w[a]|w[b]) if o else (w[a]&w[b])))
                    if not w[-1]:essential.append(x)
                dirty.append({'gate':g,'false_inputs':false_inputs,'essential_edges':essential})
        result.update(circuit=circuit,dirty=dirty)
    base.with_suffix('.result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--graph',choices=['cycle','theta233','petersen','k4sub'],default='cycle')
    p.add_argument('--cycle',type=int,default=5)
    p.add_argument('--gates',type=int,required=True)
    p.add_argument('--seconds',type=int,default=180)
    p.add_argument('--dirty',action='store_true')
    p.add_argument('--honest',action='store_true')
    p.add_argument('--ordered',action='store_true')
    p.add_argument('--solver',default='/tmp/oec/pequalnp-pilot-94/toolchain/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
    p.add_argument('--output',required=True)
    solve(p.parse_args())
