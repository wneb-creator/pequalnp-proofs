import itertools,json,subprocess,sys,time
from pathlib import Path
OUT=Path(__file__).resolve().parent
SOLVER='/tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin/cadical'
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def cl(self,*ls):self.cs.append(ls)
 def one(self,n):
  vs=[self.var() for _ in range(n)];self.cl(*vs)
  for a,b in itertools.combinations(vs,2):self.cl(-a,-b)
  return vs
 def eq(self,s,a,b):
  if isinstance(b,bool):self.cl(-s,a if b else -a)
  else:self.cl(-s,-a,b);self.cl(-s,a,-b)
 def dump(self,p):
  with p.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for cl in self.cs:f.write(' '.join(map(str,cl))+' 0\n')
def solve(P,L,E,gates,name,seconds=120):
 n=P+L;last=n+gates-1;c=CNF();sel={}
 for i in range(n,last+1):
  a,b,o=c.one(i),c.one(i),c.var();sel[i]=(a,b,o)
  for j in range(i):
   for k in range(j):c.cl(-a[j],-b[k])
 for i in range(n,last):c.cl(*(sel[j][operand][i] for j in range(i+1,last+1) for operand in (0,1)))
 def target(x):return any((x>>p)&(x>>(P+l))&1 for p,l in E)
 for x in range(1<<n):
  w=[bool((x>>i)&1) for i in range(n)]
  for i in range(n,last+1):
   a,b,o=sel[i];av,bv,v=c.var(),c.var(),c.var()
   for j in range(i):c.eq(a[j],av,w[j]);c.eq(b[j],bv,w[j])
   c.cl(o,-av,-bv,v);c.cl(o,av,-v);c.cl(o,bv,-v)
   c.cl(-o,av,bv,-v);c.cl(-o,-av,v);c.cl(-o,-bv,v)
   w.append(v)
  c.cl(w[-1] if target(x) else -w[-1])
 p=OUT/(name+'.cnf');log=OUT/(name+'.log');c.dump(p)
 print('start',name,'vars',c.n,'clauses',len(c.cs),'inputs',n,'gates',gates,flush=True)
 t=time.monotonic()
 with log.open('w') as f:r=subprocess.run([SOLVER,'-t',str(seconds),str(p)],stdout=f,stderr=subprocess.STDOUT)
 text=log.read_text();status=[line for line in text.splitlines() if line.startswith('s ')]
 print('finish',name,'elapsed',round(time.monotonic()-t,3),'return',r.returncode,'status',status,flush=True)
 if r.returncode==10:
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
  pick=lambda xs: next(i for i,v in enumerate(xs) if v in model)
  gs=[('or' if o in model else 'and',pick(a),pick(b)) for i,(a,b,o) in sel.items()]
  for x in range(1<<n):
   w=[bool((x>>i)&1) for i in range(n)]
   for op,a,b in gs:w.append(w[a] or w[b] if op=='or' else w[a] and w[b])
   assert w[-1]==target(x)
  (OUT/(name+'-witness.json')).write_text(json.dumps(gs,indent=2));print('WITNESS',gs,flush=True)
 return r.returncode
if __name__=='__main__':
 if sys.argv[1]=='c6':solve(3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)],7,'c6-size7',120)
 elif sys.argv[1]=='theta':solve(4,4,json.loads((OUT/'maximum44.json').read_text()),11,'theta-size11',300)
