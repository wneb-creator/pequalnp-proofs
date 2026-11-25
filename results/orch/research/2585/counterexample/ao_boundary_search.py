import itertools,json,subprocess,sys,time,resource
from macro_count_search import boundary_rows
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
def solve(P,L,E,gates,name,seconds=120,max_and=None,max_or=None,normal=False):
 name += "-boundary"
 n=P+L;last=n+gates-1;c=CNF();sel={}
 for i in range(n,last+1):
  a,b,o=c.one(i),c.one(i),c.var();sel[i]=(a,b,o)
  for j in range(i):
   for k in range(j):c.cl(-a[j],-b[k])
 for i in range(n,last):c.cl(*(sel[j][operand][i] for j in range(i+1,last+1) for operand in (0,1)))
 for i in range(n,last+1):
  a,b,o=sel[i]
  for j in range(i-1):c.cl(-a[j],-b[j])
  if i<last:
   aa,bb,oo=sel[i+1]
   c.cl(-a[i-1],-b[i-1],aa[i]);c.cl(-a[i-1],-b[i-1],bb[i])
   for j in range(i):
    for k in range(j):c.cl(-b[j],-bb[k])

 def atmost(lits,k):
  if k is None or k>=len(lits):return
  if k<0:c.cl();return
  prev=[]
  for lit in lits:
   cur=[c.var() for _ in range(k+1)]
   c.cl(-lit,cur[0])
   for j in range(len(prev)):c.cl(-prev[j],cur[j])
   for j in range(k):
    if j<len(prev):c.cl(-prev[j],-lit,cur[j+1])
   c.cl(-cur[k]);prev=cur
 atmost([-sel[i][2] for i in sel],max_and)
 atmost([sel[i][2] for i in sel],max_or)
 false_values={i:[] for i in sel}
 below={i:c.var() for i in sel} if normal else {}
 def target(x):return any((x>>p)&(x>>(P+l))&1 for p,l in E)
 for x,_ in boundary_rows(n,E,P):
  w=[bool((x>>i)&1) for i in range(n)]
  for i in range(n,last+1):
   a,b,o=sel[i];av,bv,v=c.var(),c.var(),c.var()
   for j in range(i):c.eq(a[j],av,w[j]);c.eq(b[j],bv,w[j])
   c.cl(o,-av,-bv,v);c.cl(o,av,-v);c.cl(o,bv,-v)
   c.cl(-o,av,bv,-v);c.cl(-o,-av,v);c.cl(-o,-bv,v)
   w.append(v)
   if normal and not target(x):false_values[i].append(v)
  c.cl(w[-1] if target(x) else -w[-1])
 if normal:
  for i in sel:
   for v in false_values[i]:c.cl(-below[i],-v)
   c.cl(below[i],*false_values[i])
   for j in range(i+1,last+1):
    a,b,o=sel[j]
    for operand in (a,b):
     c.cl(-below[i],-operand[i],o)
     c.cl(-below[i],-operand[i],below[j])
 p=OUT/(name+'.cnf');log=OUT/(name+'.log');c.dump(p)
 print('start',name,'vars',c.n,'clauses',len(c.cs),'inputs',n,'gates',gates,flush=True)
 t=time.monotonic()
 def limits():
  resource.setrlimit(resource.RLIMIT_AS,(1900*1024*1024,1900*1024*1024))
  resource.setrlimit(resource.RLIMIT_CPU,(seconds+10,seconds+10))
 with log.open('w') as f:
  try:r=subprocess.run([SOLVER,'-t',str(seconds),str(p)],stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=seconds+20)
  except subprocess.TimeoutExpired:
   f.write('\nPython outer timeout reached.\n');r=subprocess.CompletedProcess([],124)

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
  assert max_and is None or sum(op=='and' for op,a,b in gs)<=max_and
  assert max_or is None or sum(op=='or' for op,a,b in gs)<=max_or
  (OUT/(name+'-witness.json')).write_text(json.dumps(gs,indent=2));print('WITNESS',gs,flush=True)
 return r.returncode
if __name__=='__main__':
 problem=sys.argv[1];mode=sys.argv[2];gates=int(sys.argv[3]);seconds=int(sys.argv[4])
 if problem=='c6':P=L=3;E=[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)];tau=3
 elif problem=='theta':P=L=4;E=json.loads((OUT/'maximum44.json').read_text());tau=4
 elif problem=='p4':P=L=2;E=[(0,0),(1,0),(1,1)];tau=2
 elif problem=='fano':P=L=7;E=[(p,l) for p in range(7) for l in range(7) if (p-l)%7 in [0,1,3]];tau=7
 kwargs={'max_and':tau-1} if mode=='and' else {'max_or':len(E)-2} if mode=='or' else {}
 solve(P,L,E,gates,f'{problem}-{mode}-size{gates}',seconds,normal='--normal' in sys.argv,**kwargs)
