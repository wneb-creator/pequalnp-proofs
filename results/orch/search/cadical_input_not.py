import argparse,itertools,json,random,subprocess,time
from pathlib import Path
from synth_circuit import TARGET,EDGES,check

class CNF:
    def __init__(self):self.n=0;self.cs=[]
    def var(self):self.n+=1;return self.n
    def add(self,*xs):self.cs.append(tuple(xs))
    def one(self,xs):
        self.add(*xs)
        for a,b in itertools.combinations(xs,2):self.add(-a,-b)
    def save(self,path):
        with open(path,'w') as f:
            f.write(f'p cnf {self.n} {len(self.cs)}\n')
            for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')

def fixed_gates(kind):
    if kind=='input':return [(2,0,0)]
    if kind.startswith('two-neg-'):
        return [(2,0,0),(2,1 if kind=='two-neg-edge' else 2,0),(0,10,11)]
    op,relation=kind.split('-');return [(0 if op=='and' else 1,0,1 if relation=='edge' else 2),(2,10,0)]

def encode(samples,size,ordered=True,kind='input'):
    c=CNF();true=c.var();c.add(true)
    fixed=fixed_gates(kind);start=len(fixed)
    aa=[None]*start;bb=[None]*start;oo=[None]*start
    for g in range(start,size):
        a=[c.var() for _ in range(10+g)];b=[c.var() for _ in range(10+g)];o=c.var()
        aa.append(a);bb.append(b);oo.append(o);c.one(a);c.one(b)
        for j in range(10+g):
            for k in range(j+1):c.add(-a[j],-b[k])
        if ordered and g>start:
            for j in range(10+g-1):
                for k in range(j):c.add(-bb[g-1][j],-b[k])
    for g in range(size-1):
        already=any(a==10+g or (o!=2 and b==10+g) for o,a,b in fixed[g+1:])
        if not already:c.add(*(sel[10+g] for h in range(max(g+1,start),size) for sel in [aa[h],bb[h]]))
    if kind=='input':
        c.add(*(sel[0] for h in range(start,size) for sel in [aa[h],bb[h]]))
    for x in samples:
        w=[true if(x>>i)&1 else -true for i in range(10)]
        for o,a,b in fixed:
            value=(w[a]>0 and w[b]>0) if o==0 else (w[a]>0 or w[b]>0) if o==1 else not(w[a]>0)
            w.append(true if value else -true)
        for g in range(start,size):
            u,v,y=c.var(),c.var(),c.var();o=oo[g]
            for sel,val in zip(aa[g],w):c.add(-sel,-u,val);c.add(-sel,u,-val)
            for sel,val in zip(bb[g],w):c.add(-sel,-v,val);c.add(-sel,v,-val)
            c.add(-o,-y,u);c.add(-o,-y,v);c.add(-o,y,-u,-v)
            c.add(o,y,-u);c.add(o,y,-v);c.add(o,-y,u,v)
            w.append(y)
        c.add(w[-1] if(TARGET>>x)&1 else -w[-1])
    return c,aa,bb,oo

def main():
    p=argparse.ArgumentParser();p.add_argument('--solver',required=True);p.add_argument('--prefix',required=True);p.add_argument('--seconds',type=int,default=1200);p.add_argument('--seed',type=int,default=0);p.add_argument('--full',action='store_true');p.add_argument('--size',type=int,default=19);p.add_argument('--kind',choices=['input','and-edge','and-nonedge','or-edge','or-nonedge','two-neg-edge','two-neg-nonedge'],default='input');args=p.parse_args()
    rng=random.Random(args.seed)
    samples=list(range(1024)) if args.full else sorted(set([x for x in range(1024) if not((TARGET>>x)&1)]+[(1<<a)|(1<<b) for a,b in EDGES]+rng.sample(range(1024),24)))
    prefix=Path(args.prefix)
    for it in range(40):
        c,aa,bb,oo=encode(samples,args.size,kind=args.kind)
        path=prefix.with_name(prefix.name+f'-{it}.cnf');c.save(path)
        stdout=prefix.with_name(prefix.name+f'-{it}.stdout');stderr=prefix.with_name(prefix.name+f'-{it}.stderr')
        print(json.dumps({'iteration':it,'samples':len(samples),'vars':c.n,'clauses':len(c.cs),'input':str(path)}),flush=True)
        t=time.monotonic()
        with stdout.open('w') as out,stderr.open('w') as err:r=subprocess.run([args.solver,'-t',str(args.seconds),f'--seed={args.seed}',str(path)],stdout=out,stderr=err)
        print(json.dumps({'iteration':it,'returncode':r.returncode,'seconds':time.monotonic()-t}),flush=True)
        if r.returncode!=10:return
        model={int(v) for line in stdout.read_text().splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
        gates=fixed_gates(args.kind)
        for g in range(len(gates),args.size):
            a=next(i for i,v in enumerate(aa[g]) if v in model);b=next(i for i,v in enumerate(bb[g]) if v in model);o=0 if oo[g] in model else 1
            gates.append((o,a,b))
        bad=check(gates)
        print(json.dumps({'iteration':it,'gates':gates,'mismatches':len(bad)}),flush=True)
        if not bad:
            prefix.with_name(prefix.name+'-witness.json').write_text(json.dumps({'gates':gates},indent=2));print('WITNESS_FOUND',flush=True);return
        samples=sorted(set(samples+rng.sample(bad,min(32,len(bad)))))

if __name__=='__main__':main()
