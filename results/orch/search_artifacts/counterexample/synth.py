import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path

P = Path('/tmp/oec/pequalnp-pilot-99/counterexample')
SOLVER = '/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x): return any((x >> a & 1) and (x >> b & 1) for a,b in EDGES)

class CNF:
    def __init__(self): self.n = 0; self.cs = []
    def var(self): self.n += 1; return self.n
    def add(self, *ls): self.cs.append(tuple(ls))
    def one(self, vs):
        self.add(*vs)
        if len(vs) < 2: return
        prefix = [self.var() for _ in vs[:-1]]
        self.add(-vs[0], prefix[0])
        for i in range(1,len(vs)-1):
            self.add(-vs[i],prefix[i]); self.add(-prefix[i-1],prefix[i]); self.add(-vs[i],-prefix[i-1])
        self.add(-vs[-1],-prefix[-1])
    def save(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.cs)}\n')
            for c in self.cs: f.write(' '.join(map(str,c)) + ' 0\n')

def encode(rows, nots, first, fix=None, ngates=19, colex=False):
    f=CNF(); typ=[]; aa=[]; bb=[]
    for g in range(ngates):
        typ.append([f.var() for _ in range(3)]);f.one(typ[-1])
        aa.append([f.var() for _ in range(g+10)]);f.one(aa[-1])
        bb.append([f.var() for _ in range(g+10)]);f.one(bb[-1])
        # Commutative gate inputs sorted; unary negation uses the same selector twice.
        for a in range(g+10):
            for b in range(g+10):
                if a>=b:f.add(typ[g][2],-aa[g][a],-bb[g][b])
                if a!=b:f.add(-typ[g][2],-aa[g][a],-bb[g][b])
    nv=[t[2] for t in typ]
    if nots==0:
        for v in nv:f.add(-v)
    elif nots==1:f.one(nv)
    else:
        f.add(*nv)
        for xs in itertools.combinations(nv,5):f.add(*[-x for x in xs])
    # Every intermediate gate contributes to a later gate.
    for g in range(ngates-1):f.add(*[sel[g+10] for h in range(g+1,ngates) for sel in (aa[h],bb[h])])
    if colex:
        # Breadth-first topological representative: largest fanin never decreases.
        for g in range(ngates-1):
            for a in range(g+10):
                for b in range(a):f.add(-bb[g][a],-bb[g+1][b])
    # Optional first-gate orbit.
    if first:
        op,a,b=first
        f.add(typ[0][op]);f.add(aa[0][a]);f.add(bb[0][b])
    # Optional fixed prefix supplied to probe local neighborhoods.
    if fix:
        for g,(op,a,b) in fix.items():f.add(typ[g][op]);f.add(aa[g][a]);f.add(bb[g][b])
    for row in rows:
        vals=[f.var() for _ in range(ngates+10)]
        for i in range(10):f.add(vals[i] if row>>i&1 else -vals[i])
        for g in range(ngates):
            a=f.var();b=f.var();v=vals[g+10]
            for src in range(g+10):
                f.add(-aa[g][src],-a,vals[src]);f.add(-aa[g][src],a,-vals[src])
                f.add(-bb[g][src],-b,vals[src]);f.add(-bb[g][src],b,-vals[src])
            t=typ[g][0]
            f.add(-t,-v,a);f.add(-t,-v,b);f.add(-t,v,-a,-b)
            t=typ[g][1]
            f.add(-t,v,-a);f.add(-t,v,-b);f.add(-t,-v,a,b)
            t=typ[g][2]
            f.add(-t,v,a);f.add(-t,-v,-a)
        f.add(vals[-1] if target(row) else -vals[-1])
    return f,typ,aa,bb

def evaluate(gs,row):
    w=[bool(row>>i&1) for i in range(10)]
    for op,a,b in gs:w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]) if op==1 else not w[a])
    return w[-1]

def main():
    p=argparse.ArgumentParser();p.add_argument('--name',default='sat');p.add_argument('--nots',type=int,default=1);p.add_argument('--first',default='');p.add_argument('--seconds',type=int,default=300);p.add_argument('--gates',type=int,default=19);p.add_argument('--fixfile',default='');p.add_argument('--colex',action='store_true');args=p.parse_args()
    first=tuple(map(int,args.first.split(','))) if args.first else None
    fix={int(k):v for k,v in json.loads(Path(args.fixfile).read_text()).items()} if args.fixfile else None
    rows=sorted(set([x for x in range(1024) if not target(x)] + [(1<<a)|(1<<b) for a,b in EDGES]))
    for iteration in range(20):
        prefix=P/f'{args.name}-{iteration}'
        f,ts,aa,bb=encode(rows,args.nots,first,fix,args.gates,args.colex);f.save(prefix.with_suffix('.cnf'))
        prefix.with_suffix('.meta.json').write_text(json.dumps({'rows':rows,'typ':ts,'a':aa,'b':bb}))
        print('START',iteration,'rows',len(rows),'vars',f.n,'clauses',len(f.cs),flush=True)
        with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
            result=subprocess.run([SOLVER,'--sat','-t',str(args.seconds),str(prefix.with_suffix('.cnf'))],stdout=out,stderr=err)
        print('END',iteration,'exit',result.returncode,flush=True)
        if result.returncode!=10:return
        model=set()
        for line in prefix.with_suffix('.stdout').read_text().splitlines():
            if line.startswith('v '):model.update(int(s) for s in line[2:].split() if int(s)>0)
        gs=[]
        for i in range(args.gates):gs.append(tuple(next(j for j,v in enumerate(vs) if v in model) for vs in (ts[i],aa[i],bb[i])))
        bad=[x for x in range(1024) if evaluate(gs,x)!=target(x)]
        prefix.with_suffix('.circuit.json').write_text(json.dumps({'gates':gs,'bad':bad},indent=2))
        print('MODEL',gs,'mismatches',len(bad),flush=True)
        if not bad:print('VERIFIED WITNESS',args.gates,'gates',sum(op==2 for op,a,b in gs),'NOT gates',flush=True);return
        rows=sorted(set(rows+bad))

if __name__=='__main__':main()
