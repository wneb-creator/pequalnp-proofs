import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):
    return any((x >> a & 1) and (x >> b & 1) for a,b in EDGES)

class CNF:
    def __init__(self):
        self.nvars = 0
        self.clauses = []
    def var(self):
        self.nvars += 1
        return self.nvars
    def clause(self, *lits):
        self.clauses.append(list(lits))
    def one(self, xs):
        self.clause(*xs)
        for x,y in itertools.combinations(xs,2):
            self.clause(-x,-y)
    def write(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for c in self.clauses:
                f.write(' '.join(map(str,c))+' 0\n')

def encode(rows, gates, first, monotone, live, ordered, irredundant=False, notmax=None, roots_last=False):
    c = CNF()
    typ=[]; left=[]; right=[]
    for i in range(gates):
        ts=[c.var() for _ in range(3)];c.one(ts)
        if monotone:c.clause(-ts[2])
        a=[c.var() for _ in range(11+i)]
        b=[c.var() for _ in range(11+i)]
        c.one(a);c.one(b)
        # Source 0 is the free false constant; sources 1..10 are inputs.
        # Sources 11..10+i are earlier gates.
        c.clause(-ts[2],b[0])
        for aa in range(11+i):
            for bb in range(aa):
                c.clause(ts[2],-a[aa],-b[bb])
        typ.append(ts);left.append(a);right.append(b)
    c.clause(typ[-1][1])
    if roots_last:
        c.clause(left[-1][gates+8]);c.clause(right[-1][gates+9])
        c.clause(-left[-2][gates+8]);c.clause(-right[-2][gates+8])
    if irredundant:
        for i in range(gates):
            c.clause(-left[i][0])
            for a in range(1,11+i):c.clause(typ[i][2],-left[i][a],-right[i][a])
            c.clause(typ[i][2],-right[i][0])
        for a in range(1,11):
            c.clause(*[pin[a] for i in range(gates) for pin in [left[i],right[i]]])
        for a in range(11):
            c.clause(-left[-1][a]);c.clause(-right[-1][a])
    if notmax is not None and notmax < gates:
        for ns in itertools.combinations([ts[2] for ts in typ],notmax+1):c.clause(*[-n for n in ns])
    if first:
        op, a,b=first
        c.clause(typ[0][op]);c.clause(left[0][a]);c.clause(right[0][b])
    if live:
        for i in range(gates-1):
            c.clause(*[pin[11+i] for j in range(i+1,gates) for pin in [left[j],right[j]]])
    if ordered:
        # If consecutive gates have no dependency, sort by their (left,right,op) tuple.
        # This is only a search heuristic, never used as an unsatisfiability proof.
        for i in range(gates-1):
            dep=right[i+1][11+i]
            dep2=left[i+1][11+i]
            for aa in range(11+i):
                for ab in range(aa):
                    c.clause(dep,dep2,-left[i][aa],-left[i+1][ab])
    for row in rows:
        values=[c.var() for _ in range(11+gates)]
        c.clause(-values[0])
        for a in range(10):c.clause(values[1+a] if row >> a & 1 else -values[1+a])
        for i in range(gates):
            p=c.var();q=c.var();v=values[11+i]
            for j,s in enumerate(left[i]):
                c.clause(-s,-p,values[j]);c.clause(-s,p,-values[j])
            for j,s in enumerate(right[i]):
                c.clause(-s,-q,values[j]);c.clause(-s,q,-values[j])
            a,o,n=typ[i]
            c.clause(-a,-v,p);c.clause(-a,-v,q);c.clause(-a,v,-p,-q)
            c.clause(-o,v,-p);c.clause(-o,v,-q);c.clause(-o,-v,p,q)
            c.clause(-n,-v,-p);c.clause(-n,v,p)
        c.clause(values[-1] if target(row) else -values[-1])
    return c,typ,left,right

def parse_model(text):
    return {int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}

def evaluate(gs,row):
    vals=[False]+[bool(row>>a&1) for a in range(10)]
    for op,a,b in gs:
        vals.append((vals[a] and vals[b]) if op==0 else (vals[a] or vals[b]) if op==1 else not vals[a])
    return vals

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--solver',required=True)
    p.add_argument('--dir',required=True)
    p.add_argument('--time',type=int,default=600)
    p.add_argument('--gates',type=int,default=19)
    p.add_argument('--first',default='')
    p.add_argument('--monotone',action='store_true')
    p.add_argument('--live',action='store_true')
    p.add_argument('--ordered',action='store_true')
    p.add_argument('--seed',type=int,default=0)
    p.add_argument('--allrows',action='store_true')
    p.add_argument('--irredundant',action='store_true')
    p.add_argument('--notmax',type=int)
    p.add_argument('--roots-last',action='store_true')
    args=p.parse_args()
    dest=Path(args.dir);dest.mkdir(parents=True,exist_ok=True)
    rows=list(range(1024)) if args.allrows else [x for x in range(1024) if x.bit_count()<=2 or not target(x)]
    first=tuple(map(int,args.first.split(','))) if args.first else None
    start=time.monotonic()
    for iteration in range(100):
        c,typ,left,right=encode(rows,args.gates,first,args.monotone,args.live,args.ordered,args.irredundant,args.notmax,args.roots_last)
        cnfpath=dest/f'round{iteration}.cnf';c.write(cnfpath)
        print('round',iteration,'rows',len(rows),'vars',c.nvars,'clauses',len(c.clauses),flush=True)
        log=dest/f'round{iteration}.log'
        with log.open('w') as out:
            result=subprocess.run([args.solver,'-t',str(args.time),'--seed='+str(args.seed),'--sat',str(cnfpath)],stdout=out,stderr=subprocess.STDOUT)
        text=log.read_text()
        print('solver exit',result.returncode,'elapsed',time.monotonic()-start,flush=True)
        if result.returncode!=10:
            print('UNSAT' if result.returncode==20 else 'UNKNOWN',flush=True)
            return
        model=parse_model(text)
        def chosen(xs):return next(i for i,v in enumerate(xs) if v in model)
        gs=[(chosen(typ[i]),chosen(left[i]),chosen(right[i])) for i in range(args.gates)]
        (dest/f'round{iteration}-model.json').write_text(json.dumps(gs))
        misses=[x for x in range(1024) if evaluate(gs,x)[-1]!=target(x)]
        print('bad truth rows',len(misses),misses[:20],flush=True)
        if not misses:
            witnesses=[[],[]]
            a,b=gs[-1][1:]
            for x in range(1024):
                vals=evaluate(gs,x)
                if vals[a] and not vals[b]:witnesses[0].append(x)
                if vals[b] and not vals[a]:witnesses[1].append(x)
            print('WITNESS',gs,'incomparability examples',[w[:4] for w in witnesses],flush=True)
            (dest/'witness.json').write_text(json.dumps({'gates':gs,'incomparability':witnesses}))
            return
        rows=sorted(set(rows+misses))
    print('iteration cap reached',flush=True)

if __name__=='__main__':main()
