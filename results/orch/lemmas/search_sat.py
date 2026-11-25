import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N = 10
TARGET = [any((x>>a&1) and (x>>b&1) for a,b in EDGES) for x in range(1024)]

class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []
    def var(self):
        self.n += 1
        return self.n
    def add(self,*lits):
        if True in [x for x in lits if isinstance(x,bool)]: return
        self.clauses.append([x for x in lits if not isinstance(x,bool)])
    def one(self,vs):
        self.add(*vs)
        for a,b in itertools.combinations(vs,2): self.add(-a,-b)
    def out(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for c in self.clauses: f.write(' '.join(map(str,c))+' 0\n')

def neg(x): return not x if isinstance(x,bool) else -x

def encode(samples, gates=19, first=None, one_not=False, fixed=None, require_not=True, signed=False, useful=True):
    c=CNF()
    ops=[[c.var() for _ in range(8 if signed else 3)] for _ in range(gates)]
    aa=[[c.var() for _ in range(N+j)] for j in range(gates)]
    bb=[[c.var() for _ in range(N+j)] for j in range(gates)]
    for j in range(gates):
        c.one(ops[j]);c.one(aa[j]);c.one(bb[j])
        if signed:
            for k in (3,4,5,6):c.add(-ops[j][k])
        if not signed: c.add(-ops[j][2],bb[j][0])
        for a in range(N+j):
            for b in range(a+1):
                if signed: c.add(-aa[j][a],-bb[j][b])
                else: c.add(ops[j][2],-aa[j][a],-bb[j][b])
    nt=[o[2] for o in ops]
    if one_not and not signed: c.one(nt)
    elif require_not and not signed: c.add(*nt)
    # Every counted gate except the output is useful in the normalized search domain.
    if useful:
        for j in range(gates-1):
            c.add(*(aa[k][N+j] for k in range(j+1,gates)),*(bb[k][N+j] for k in range(j+1,gates)))
    if first is not None:
        op,a,b=[(0,0,1),(0,0,2),(1,0,1),(1,0,2),(2,0,0)][first]
        c.add(ops[0][op]);c.add(aa[0][a]);c.add(bb[0][b])
    if fixed:
        for j,(op,a,b) in fixed.items():
            c.add(ops[j][op]);c.add(aa[j][a]);c.add(bb[j][b])
    for x in samples:
        v=[bool(x>>i&1) for i in range(N)]
        for j in range(gates):
            a,b,z=c.var(),c.var(),c.var()
            for av,bv,src in zip(aa[j],bb[j],v):
                c.add(-av,-a,src);c.add(-av,a,neg(src))
                c.add(-bv,-b,src);c.add(-bv,b,neg(src))
            op=ops[j]
            if signed:
                for k in range(8):
                    for va,vb in itertools.product((False,True),repeat=2):
                        val=signed_eval(k,va,vb)
                        c.add(-op[k],-a if va else a,-b if vb else b,z if val else -z)
            else:
                c.add(-op[0],-a,-b,z);c.add(-op[0],a,-z);c.add(-op[0],b,-z)
                c.add(-op[1],a,b,-z);c.add(-op[1],-a,z);c.add(-op[1],-b,z)
                c.add(-op[2],-a,-z);c.add(-op[2],a,z)
            v.append(z)
        c.add(v[-1] if TARGET[x] else -v[-1])
    return c,ops,aa,bb

def signed_eval(op,a,b):
    return ((not a if op&1 else a) and (not b if op&2 else b)) != bool(op&4)

def verify(model,signed=False):
    bad=[]
    for x in range(1<<N):
        v=[bool(x>>i&1) for i in range(N)]
        for op,a,b in model:
            v.append(signed_eval(op,v[a],v[b]) if signed else v[a] and v[b] if op==0 else v[a] or v[b] if op==1 else not v[a])
        if v[-1]!=TARGET[x]:bad.append(x)
    return bad

def main():
    global EDGES,N,TARGET
    ap=argparse.ArgumentParser()
    ap.add_argument('--solver',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--first',type=int)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--one-not',action='store_true')
    ap.add_argument('--signed',action='store_true')
    ap.add_argument('--gates',type=int,default=19)
    ap.add_argument('--delete-nine',action='store_true')
    ap.add_argument('--repair')
    ap.add_argument('--changes',type=int,default=3)
    ap.add_argument('--not-count',type=int)
    ap.add_argument('--colex',action='store_true')
    ap.add_argument('--samples',choices=['core','layered','full'],default='core')
    ap.add_argument('--primary-retained',action='store_true')
    ap.add_argument('--strict-order',action='store_true')
    ap.add_argument('--backend',choices=['cadical','kissat'],default='cadical')
    args=ap.parse_args()
    if args.strict_order:args.colex=True
    if args.delete_nine:
        N=9;EDGES=[(a,b) for a,b in EDGES if a!=9 and b!=9]
        TARGET=[any((x>>a&1) and (x>>b&1) for a,b in EDGES) for x in range(1<<N)]
    root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    samples=sorted(set([x for x in range(1<<N) if not TARGET[x]]+[(1<<a)|(1<<b) for a,b in EDGES]))
    if args.samples=='layered':samples=sorted(set(samples+[x for x in range(1<<N) if x.bit_count()==3 or x.bit_count()>=N-2]))
    elif args.samples=='full':samples=list(range(1<<N))
    for iteration in range(20):
        c,ops,aa,bb=encode(samples,gates=args.gates,first=args.first,one_not=args.one_not,signed=args.signed,useful=not bool(args.repair))
        if args.not_count is not None:
            ns=[op[2] for op in ops]
            for vs in itertools.combinations(ns,args.not_count+1):c.add(*(-v for v in vs))
            for vs in itertools.combinations(ns,len(ns)-args.not_count+1):c.add(*vs)
        if args.colex:
            for j in range(args.gates-1):
                for a in range(N+j):
                    for b in range(a):
                        if args.signed:c.add(-bb[j][a],-bb[j+1][b])
                        else:
                            p,q=ops[j][2],ops[j+1][2]
                            c.add(p,q,-bb[j][a],-bb[j+1][b])
                            c.add(p,-q,-bb[j][a],-aa[j+1][b])
                            c.add(-p,q,-aa[j][a],-bb[j+1][b])
                            c.add(-p,-q,-aa[j][a],-aa[j+1][b])
        if args.strict_order:
            for j in range(args.gates-1):
                for b in range(N+j):
                    for a in range(b):
                        for smaller in range(a):
                            c.add(-bb[j][b],-bb[j+1][b],-aa[j][a],-aa[j+1][smaller])
                        valid_ops=(0,1,2,7) if args.signed else (0,1)
                        for p in valid_ops:
                            for q in valid_ops:
                                if p>=q:
                                    c.add(-bb[j][b],-bb[j+1][b],-aa[j][a],-aa[j+1][a],-ops[j][p],-ops[j+1][q])
                    if not args.signed:
                        p,q=ops[j][2],ops[j+1][2]
                        c.add(p,-q,-bb[j][b],-aa[j+1][b])
                        c.add(-p,-q,-aa[j][b],-aa[j+1][b])
        if args.primary_retained:
            uses=[[c.var() for _ in range(N)] for _ in range(args.gates)]
            for j in range(args.gates):
                for a in range(N):
                    u,p,q=uses[j][a],aa[j][a],bb[j][a]
                    c.add(-p,u)
                    if args.signed:
                        c.add(-q,u);c.add(-u,p,q)
                    else:
                        nt=ops[j][2]
                        c.add(-q,nt,u);c.add(-u,p,q);c.add(-u,p,-nt)
            for j in (range(1) if args.signed else range(args.gates)):
                for a,b in itertools.combinations(range(N),2):
                    for v in (a,b):
                        c.add(-aa[j][a],-bb[j][b],*(uses[k][v] for k in range(args.gates) if k!=j))
        if args.repair:
            base=json.loads(Path(args.repair).read_text())
            edits=[c.var() for _ in base]
            for j,(op,a,b) in enumerate(base):
                if args.signed:
                    if a>b:a,b,op=b,a,((op&1)<<1)|((op&2)>>1)|(op&4)
                elif op==2:b=0
                elif a>b:a,b=b,a
                c.add(edits[j],ops[j][op]);c.add(edits[j],aa[j][a]);c.add(edits[j],bb[j][b])
            for xs in itertools.combinations(edits,args.changes+1):c.add(*(-x for x in xs))
        cnf=root/f'{iteration}.cnf';sol=root/f'{iteration}.sol';log=root/f'{iteration}.log'
        c.out(cnf)
        print('solve',iteration,'samples',len(samples),'variables',c.n,'clauses',len(c.clauses),flush=True)
        del c
        with log.open('w') as f:
            cmd=([args.solver,'-t',str(args.seconds),'--seed='+str(args.seed),'-w',str(sol),str(cnf)] if args.backend=='cadical' else
                 [args.solver,'--sat','--time='+str(args.seconds),'--seed='+str(args.seed),str(cnf)])
            run=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
        print('exit',run.returncode,flush=True)
        if run.returncode!=10:return
        positive=set()
        for line in (sol if args.backend=='cadical' else log).read_text().splitlines():
            if line.startswith('v '):positive.update(int(x) for x in line.split()[1:] if int(x)>0)
        model=[[next(k for k,a in enumerate(v) if a in positive) for v in (ops[j],aa[j],bb[j])] for j in range(args.gates)]
        bad=verify(model,args.signed)
        print('counterexamples',len(bad),'model',model,flush=True)
        (root/f'{iteration}-model.json').write_text(json.dumps(model))
        if not bad:
            print('VERIFIED ALL',1<<N,flush=True);return
        samples=sorted(set(samples+bad[:64]))

if __name__=='__main__': main()
