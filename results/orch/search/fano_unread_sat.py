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
    if name == 'path4':
        return 4, [(0,1),(1,2),(2,3)], []
    if name == 'k4inc':
        es=list(itertools.combinations(range(4),2))
        return 10,[(v,4+i) for i,e in enumerate(es) for v in e],[(0,1),(0,4),(2,4),(4,5),(6,7)]
    if name == 'fano':
        return 14,[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)],[(0,1),(0,7),(2,7)]
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
    tests=positives+negatives+([1 << i for i in range(n)] if args.propagate else [])
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
    if args.edge_stabilizer:
        assert args.graph == 'fano' and args.unread_point == 0 and args.unread_line == 7
        representatives = {(0,1),(0,2),(1,2),(1,3),(2,4),(4,5),(0,7),(1,7),(2,7),(1,8),(2,8),(3,8),(5,8),(1,11)}
        for i, j in itertools.combinations(range(n), 2):
            if (i,j) not in representatives:
                cnf.clause(-sels[0][0][i], -sels[0][1][j])
    for g in range(k-1):cnf.clause(*(sels[h][b][n+g] for h in range(g+1,k) for b in range(2)))
    if args.ordered:
        for g in range(k-1):
            for i in range(n+g):
                for j in range(i):cnf.clause(-sels[g][1][i],-sels[g+1][1][j])
    if args.min_ands > k:
        cnf.clause()
    elif args.min_ands > 0:
        bound = k - args.min_ands
        previous = [True] + [False] * (bound + 1)
        for op in ops:
            current = [True] + [cnf.var() for _ in range(bound + 1)]
            for j in range(1, bound + 2):
                cnf.clause(neg(previous[j]), current[j])
                cnf.clause(-op, neg(previous[j-1]), current[j])
            previous = current
        cnf.clause(-previous[bound+1])
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
    # Exact squarefree proof states on one fixed prime edge.  State bits
    # represent singleton p, singleton l, and the pair {p,l}.  No AO2 proof
    # tree is empty, so a pair at an AND must join opposite singletons.
    ep, el = args.unread_point, args.unread_line
    assert ep != el and 0 <= ep < n and 0 <= el < n
    assert target((1 << ep) | (1 << el))
    read = [[cnf.var() for _ in range(3)] for _ in range(k)]
    read_operands = [[[cnf.var() for _ in range(3)] for _ in range(2)] for _ in range(k)]
    for g in range(k):
        for side in range(2):
            for i, sel in enumerate(sels[g][side]):
                for bit in range(3):
                    value = ((i == ep and bit == 0) or (i == el and bit == 1)) if i < n else read[i-n][bit]
                    z = read_operands[g][side][bit]
                    cnf.clause(-sel, neg(value), z)
                    cnf.clause(-sel, value, -z)
        a, b = read_operands[g]
        op = ops[g]
        for bit in range(3):
            z = read[g][bit]
            # op=true means OR.
            cnf.clause(-op, -a[bit], z)
            cnf.clause(-op, -b[bit], z)
            cnf.clause(-op, a[bit], b[bit], -z)
        for bit in range(2):
            cnf.clause(op, -read[g][bit])
        joins = []
        for av, bv in [(a[0], b[1]), (a[1], b[0])]:
            term = cnf.var()
            joins.append(term)
            cnf.clause(-term, av)
            cnf.clause(-term, bv)
            cnf.clause(term, -av, -bv)
        z = read[g][2]
        cnf.clause(op, -joins[0], z)
        cnf.clause(op, -joins[1], z)
        cnf.clause(op, joins[0], joins[1], -z)
    cnf.clause(read[-1][2] if args.require_read else -read[-1][2])
    if args.propagate:
        edge_test = tests.index((1 << ep) | (1 << el))
        for g in range(k):
            for bit in range(3):
                cnf.clause(-read[g][bit], vals[g][edge_test])
            cnf.clause(-read[g][0], vals[g][tests.index(1 << ep)])
            cnf.clause(-read[g][1], vals[g][tests.index(1 << el)])
        cnf.clause(-read[-1][0])
        cnf.clause(-read[-1][1])
    base=Path(args.output)
    cnf.write(base.with_suffix('.cnf'))
    start=time.monotonic()
    with base.with_suffix('.solver.stdout').open('w') as out,base.with_suffix('.solver.stderr').open('w') as err:
        proc=subprocess.run([args.solver,'-t',str(args.seconds),str(base.with_suffix('.cnf'))],stdout=out,stderr=err)
    result={'graph':args.graph,'n':n,'edges':edges,'gates':k,'tests':len(tests),'variables':cnf.n,'clauses':len(cnf.rows),'seconds':time.monotonic()-start,'returncode':proc.returncode,'status':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(proc.returncode,'ERROR'),'ordered':args.ordered,'edge_stabilizer':args.edge_stabilizer,'propagate':args.propagate,'min_ands':args.min_ands}
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
        proof_states = [{1} if i == ep else {2} if i == el else set() for i in range(n)]
        for op, a, b in circuit:
            proof_states.append(proof_states[a] | proof_states[b] if op else
                {u | v for u in proof_states[a] for v in proof_states[b] if not (u & v)})
        actual_read = 3 in proof_states[-1]
        assert actual_read == args.require_read
        result.update(circuit=circuit,dirty=dirty, fixed_edge=[ep,el], fixed_edge_read1=actual_read)
    base.with_suffix('.result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--graph',choices=['fano','k4inc','cycle','theta233','petersen','k4sub','path4'],default='fano')
    p.add_argument('--cycle',type=int,default=5)
    p.add_argument('--gates',type=int,required=True)
    p.add_argument('--seconds',type=int,default=180)
    p.add_argument('--dirty',action='store_true')
    p.add_argument('--honest',action='store_true')
    p.add_argument('--ordered',action='store_true')
    p.add_argument('--unread-point',type=int,default=0)
    p.add_argument('--unread-line',type=int,default=7)
    p.add_argument('--require-read',action='store_true')
    p.add_argument('--edge-stabilizer',action='store_true')
    p.add_argument('--propagate',action='store_true')
    p.add_argument('--min-ands',type=int,default=0)
    p.add_argument('--solver',default='/tmp/oec/pequalnp-pilot-94/toolchain/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
    p.add_argument('--output',required=True)
    solve(p.parse_args())
