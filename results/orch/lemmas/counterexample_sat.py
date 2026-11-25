"""Bounded SAT witness search, not a certified lower-bound proof."""
import argparse
import json
from pathlib import Path
import subprocess
import time

EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(s):
    return any((s>>a&1) and (s>>b&1) for a,b in EDGES)

class CNF:
    def __init__(self): self.variables=0;self.clauses=[]
    def new(self): self.variables+=1;return self.variables
    def add(self,*lits):
        if True in [x for x in lits if isinstance(x,bool)]: return
        self.clauses.append([x for x in lits if not isinstance(x,bool)])
    def one(self,xs):
        self.add(*xs)
        for i,a in enumerate(xs):
            for b in xs[:i]: self.add(-a,-b)
    def eqguard(self,g,a,b):
        if isinstance(b,bool): self.add(-g,a if b else -a)
        else:self.add(-g,-a,b);self.add(-g,a,-b)
    def write(self,p):
        with p.open('w') as f:
            f.write(f'p cnf {self.variables} {len(self.clauses)}\n')
            for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')

def encode(rows,gates,first,normalized=False):
    c=CNF();choices=[];nots=[]
    for i in range(gates):
        a=[c.new() for _ in range(11+i)];b=[c.new() for _ in range(11+i)]
        c.one(a);c.one(b)
        n=c.new();o=c.new();nots.append(n)
        c.add(-n,b[0])
        for x in range(len(a)):
            for y in range(x):c.add(n,-a[x],-b[y])
        choices.append((a,b,n,o))
    c.add(*nots)
    if normalized:
        # A witness-search restriction: no constant reads or binary identities,
        # and every gate feeds a later gate (therefore the last output).
        for a,b,n,o in choices:
            c.add(-a[10]);c.add(-b[10])
            for x in range(len(a)):c.add(n,-a[x],-b[x])
        for i in range(gates-1):
            c.add(*(x for a,b,n,o in choices[i+1:] for x in (a[11+i],b[11+i])))
    if first!='any':
        op,x,y={'and_edge':(0,0,1),'and_nonedge':(0,0,2),'or_edge':(1,0,1),'or_nonedge':(1,0,2),'not':(2,0,0)}[first]
        a,b,n,o=choices[0]
        c.add(a[x]);c.add(b[y]);c.add(n if op==2 else -n)
        if op!=2:c.add(o if op==1 else -o)
    for s in rows:
        wires=[bool(s>>i&1) for i in range(10)]+[False]
        for a,b,n,o in choices:
            av=c.new();bv=c.new();z=c.new()
            for choose,value in zip(a,wires):c.eqguard(choose,av,value)
            for choose,value in zip(b,wires):c.eqguard(choose,bv,value)
            # n -> z = !av.
            c.add(-n,z,av);c.add(-n,-z,-av)
            # !n & o -> z = av OR bv.
            c.add(n,-o,z,-av);c.add(n,-o,z,-bv);c.add(n,-o,-z,av,bv)
            # !n & !o -> z = av AND bv.
            c.add(n,o,-z,av);c.add(n,o,-z,bv);c.add(n,o,z,-av,-bv)
            wires.append(z)
        c.add(wires[-1] if target(s) else -wires[-1])
    return c,choices

def decode(truth,choices):
    gs=[]
    for a,b,n,o in choices:
        x=next(i for i,v in enumerate(a) if v in truth)
        y=next(i for i,v in enumerate(b) if v in truth)
        gs.append((2 if n in truth else 1 if o in truth else 0,x,y))
    return gs

def check(gs):
    wrong=[]
    for s in range(1024):
        w=[bool(s>>i&1) for i in range(10)]+[False]
        for op,a,b in gs:w.append(not w[a] if op==2 else w[a] or w[b] if op==1 else w[a] and w[b])
        if w[-1]!=target(s):wrong.append(s)
    return wrong

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--first',default='any');ap.add_argument('--seed',type=int,default=2592);ap.add_argument('--gates',type=int,default=19);ap.add_argument('--normalized',action='store_true');ap.add_argument('--samples',choices=['all-independent','maximal'],default='all-independent');ap.add_argument('--out',type=Path,required=True);ap.add_argument('--solver',required=True);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    rows=sorted(set([s for s in range(1024) if not target(s)]+[(1<<a)|(1<<b) for a,b in EDGES]))
    if args.samples=='maximal':
        rows=sorted(set([0]+[1<<i for i in range(10)]+[(1<<a)|(1<<b) for a,b in EDGES]+[s for s in range(1024) if not target(s) and all(target(s|(1<<i)) for i in range(10) if not s>>i&1)]))
    begin=time.monotonic()
    for iteration in range(20):
        cnf,choices=encode(rows,args.gates,args.first,args.normalized)
        stem=args.out/f'iteration-{iteration:02d}';cnf.write(stem.with_suffix('.cnf'))
        print('ITERATION',iteration,'rows',len(rows),'variables',cnf.variables,'clauses',len(cnf.clauses),flush=True)
        remaining=max(1,args.seconds-int(time.monotonic()-begin))
        with stem.with_suffix('.stdout').open('w') as stdout,stem.with_suffix('.stderr').open('w') as stderr:
            r=subprocess.run([args.solver,'-q','-t',str(remaining),f'--seed={args.seed}',str(stem.with_suffix('.cnf'))],stdout=stdout,stderr=stderr)
        text=stem.with_suffix('.stdout').read_text()
        print('SOLVER_EXIT',r.returncode,'elapsed',round(time.monotonic()-begin,2),flush=True)
        if r.returncode==20:
            print('UNSAT restricted normalized search instance; no general lower-bound claim',flush=True);return
        if r.returncode!=10:return
        truth={int(x) for line in text.splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
        gs=decode(truth,choices);wrong=check(gs)
        stem.with_suffix('.json').write_text(json.dumps({'gates':gs,'mismatches':wrong},indent=2))
        print('MISMATCHES',len(wrong),flush=True)
        if not wrong:
            (args.out/'witness.json').write_text(json.dumps({'gates':gs,'false_wire':10,'circuit_wire_mapping':'inputs 0..9; abstract 10 is forward-wire false; abstract 11+j maps to actual 10+j','output':10+args.gates-1},indent=2))
            print('WITNESS',flush=True);return
        rows=sorted(set(rows+wrong))
        if time.monotonic()-begin>=args.seconds:return

if __name__=='__main__':main()
