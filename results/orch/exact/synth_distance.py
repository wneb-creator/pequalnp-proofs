import argparse,itertools,json,random,subprocess,time
from pathlib import Path

EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
TARGET=[int(any((x>>a)&(x>>b)&1 for a,b in EDGES)) for x in range(1024)]
class CNF:
 def __init__(self): self.n=0;self.cl=[]
 def var(self): self.n+=1;return self.n
 def clause(self,*l): self.cl.append(l)
 def one(self,vs):
  self.clause(*vs)
  for a,b in itertools.combinations(vs,2):self.clause(-a,-b)
 def write(self,p):
  with open(p,'w') as f:
   f.write(f'p cnf {self.n} {len(self.cl)}\n')
   for c in self.cl:f.write(' '.join(map(str,c))+' 0\n')

def encode(m,samples,first,notcount,seed):
 c=CNF(); L=[];R=[];O=[]
 for i in range(m):
  n=10+i
  l=[c.var() for _ in range(n)];r=[c.var() for _ in range(n)];o=[c.var() for _ in range(3)]
  L.append(l);R.append(r);O.append(o)
  c.one(l);c.one(r);c.one(o)
  for a in range(n):
   for b in range(n):
    if a>b:c.clause(o[2],-l[a],-r[b])
    if a==b:c.clause(o[2],-l[a],-r[b])
    if a!=b:c.clause(-o[2],-l[a],-r[b])
 for i in range(m-1):
  c.clause(*(L[j][10+i] for j in range(i+1,m)),*(R[j][10+i] for j in range(i+1,m)))
 c.clause(-O[-1][2])
 for k in range(10):c.clause(*(L[j][k] for j in range(m)),*(R[j][k] for j in range(m)))
 if notcount==1:c.one([o[2] for o in O])
 elif notcount==0:
  for o in O:c.clause(-o[2])
 else:c.clause(*(o[2] for o in O))
 if first>=0:
  if first==4:c.clause(O[0][2]);c.clause(L[0][0]);c.clause(R[0][0])
  else:
   c.clause(O[0][first//2]);c.clause(L[0][0]);c.clause(R[0][1+(first%2)])
 if seed is not None:
  keep=seed.get('keep',[]);gates=seed['gates']
  if 'distance' in seed:
   changes=[c.var() for _ in range(m)]
   for xs in itertools.combinations(changes,seed['distance']+1):c.clause(*(-x for x in xs))
   for i,g in enumerate(gates):
    op=['and','or','not'].index(g['op'])
    c.clause(changes[i],O[i][op]);c.clause(changes[i],L[i][g['a']]);c.clause(changes[i],R[i][g.get('b',g['a'])])
  for i in keep:
   g=gates[i];op=['and','or','not'].index(g['op'])
   c.clause(O[i][op]);c.clause(L[i][g['a']]);c.clause(R[i][g.get('b',g['a'])])
 for x in samples:
  V=[c.var() for _ in range(10+m)]
  for k in range(10):c.clause(V[k] if (x>>k)&1 else -V[k])
  for i in range(m):
   a=c.var();b=c.var();z=V[10+i]
   for j in range(10+i):
    c.clause(-L[i][j],-a,V[j]);c.clause(-L[i][j],a,-V[j])
    c.clause(-R[i][j],-b,V[j]);c.clause(-R[i][j],b,-V[j])
   opand,opor,opnot=O[i]
   c.clause(-opand,-z,a);c.clause(-opand,-z,b);c.clause(-opand,z,-a,-b)
   c.clause(-opor,z,-a);c.clause(-opor,z,-b);c.clause(-opor,-z,a,b)
   c.clause(-opnot,-z,-a);c.clause(-opnot,z,a)
  c.clause(V[-1] if TARGET[x] else -V[-1])
 return c,L,R,O

def evaluate(gs):
 bad=[]
 for x in range(1024):
  v=[(x>>i)&1 for i in range(10)]
  for g in gs:
   a=v[g['a']];b=v[g['b']];op=g['op']
   v.append((a&b) if op=='and' else ((a|b) if op=='or' else 1-a))
  if v[-1]!=TARGET[x]:bad.append(x)
 return bad

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,default=19);ap.add_argument('--first',type=int,default=-1);ap.add_argument('--notcount',type=int,default=1);ap.add_argument('--seed',type=int,default=98);ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--rounds',type=int,default=10);ap.add_argument('--dir',required=True);ap.add_argument('--fixed');ap.add_argument('--samples');args=ap.parse_args()
 out=Path(args.dir);out.mkdir(parents=True,exist_ok=True);rng=random.Random(args.seed)
 samples=set([0,1023]+[1<<k for k in range(10)]+[(1<<a)|(1<<b) for a,b in itertools.combinations(range(10),2)])
 if args.samples:samples.update(json.loads(Path(args.samples).read_text()))
 samples.update(rng.sample(range(1024),16))
 fixed=json.loads(Path(args.fixed).read_text()) if args.fixed else None
 start=time.time()
 for it in range(args.rounds):
  c,L,R,O=encode(args.m,sorted(samples),args.first,args.notcount,fixed)
  cnf=out/f'round-{it:02d}.cnf';log=out/f'round-{it:02d}.log';c.write(cnf)
  print(f'round {it} samples={len(samples)} vars={c.n} clauses={len(c.cl)} elapsed={time.time()-start:.1f}',flush=True)
  with log.open('w') as f:
   try:p=subprocess.run(['/tmp/oec/pequalnp-pilot-98/exact/kissat/build/kissat',f'--seed={args.seed}',f'--time={args.seconds}',str(cnf)],stdout=f,stderr=subprocess.STDOUT,timeout=args.seconds+30)
   except subprocess.TimeoutExpired:
    print('timeout',flush=True);break
  s=log.read_text()
  if p.returncode!=10:
   print(f'solver exit {p.returncode}',flush=True);break
  vs=set()
  for line in s.splitlines():
   if line.startswith('v '):vs.update(int(z) for z in line.split()[1:] if int(z)>0)
  gs=[]
  for i in range(args.m):
   a=next(j for j,v in enumerate(L[i]) if v in vs);b=next(j for j,v in enumerate(R[i]) if v in vs);op=next(j for j,v in enumerate(O[i]) if v in vs)
   gs.append(dict(op=['and','or','not'][op],a=a,b=b))
  bad=evaluate(gs)
  (out/f'candidate-{it:02d}.json').write_text(json.dumps(dict(gates=gs,bad=bad),indent=2))
  print(f'candidate bad={len(bad)}',flush=True)
  if not bad:
   print('WITNESS '+json.dumps(gs),flush=True);break
  rng.shuffle(bad);samples.update(bad[:32]);(out/'samples.json').write_text(json.dumps(sorted(samples)))
if __name__=='__main__':main()
