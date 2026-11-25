import argparse,itertools,json,random,subprocess,time
from pathlib import Path
N=14
E=[(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
MASK=(1<<(1<<N))-1
X=[sum(1<<j for j in range(1<<N) if j>>i&1) for i in range(N)]
TARGET=0
for a,b in E:TARGET|=X[a]&X[b]
class CNF:
 def __init__(self):self.n=0;self.clauses=[]
 def var(self):self.n+=1;return self.n
 def add(self,*lits):self.clauses.append(tuple(lits))
 def one(self,ls):
  self.add(*ls)
  for a,b in itertools.combinations(ls,2):self.add(-a,-b)
 def mux(self,sel,a,v):
  if isinstance(v,bool):self.add(-sel,a if v else -a)
  else:self.add(-sel,-a,v);self.add(-sel,a,-v)
 def write(self,path):
  with path.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.clauses)}\n')
   for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')
def make(samples,S,fixed=None,unlocked=None,cone=False,ordered=False,distinct=False,not_count=None,no_constants=False):
 c=CNF();ops=[];lhs=[];rhs=[]
 for j in range(S):
  op=[c.var() for _ in range(3)];aa=[c.var() for _ in range(N+j+1)];bb=[c.var() for _ in range(N+j+1)]
  ops.append(op);lhs.append(aa);rhs.append(bb)
  c.one(op);c.one(aa);c.one(bb)
  for a in range(N+j+1):
   for b in range(a):
    c.add(-op[0],-aa[a],-bb[b]);c.add(-op[1],-aa[a],-bb[b])
  c.add(-op[2],bb[-1])
  if no_constants:
   c.add(-op[0],-bb[-1]);c.add(-op[2],-aa[-1])
  if distinct:
   for a in range(N+j+1):
    c.add(-op[0],-aa[a],-bb[a]);c.add(-op[1],-aa[a],-bb[a])
  if fixed is not None and j not in unlocked:
   o,a,b=fixed[j]
   if a==-1:a=N+j
   if b==-1 or o==2:b=N+j
   if o<2 and a>b:a,b=b,a
   c.add(op[o]);c.add(aa[a]);c.add(bb[b])
 if not_count is not None:
  nv=[o[2] for o in ops]
  for comb in itertools.combinations(nv,not_count+1):c.add(*[-v for v in comb])
  for comb in itertools.combinations(nv,S-not_count+1):c.add(*comb)
 if ordered:
  for j in range(S-1):
   for a,sa in enumerate(rhs[j]):
    for b in range(a):c.add(-sa,-rhs[j+1][b])
 if cone:
  for w in range(N+S-1):
   uses=[]
   for j in range(max(0,w-N+1),S):
    uses.extend([lhs[j][w],rhs[j][w]])
   c.add(*uses)
 for x in samples:
  ws=[bool(x>>i&1) for i in range(N)]
  for j in range(S):
   a,b,z=c.var(),c.var(),c.var()
   for sel,w in zip(lhs[j],ws+[False]):c.mux(sel,a,w)
   for sel,w in zip(rhs[j],ws+[False]):c.mux(sel,b,w)
   o=ops[j]
   c.add(-o[0],-a,-b,z);c.add(-o[0],a,-z);c.add(-o[0],b,-z)
   c.add(-o[1],a,b,-z);c.add(-o[1],-a,z);c.add(-o[1],-b,z)
   c.add(-o[2],a,z);c.add(-o[2],-a,-z)
   ws.append(z)
  c.add(ws[-1] if TARGET>>x&1 else -ws[-1])
 return c,(ops,lhs,rhs)
def decode(model,schema):
 gs=[]
 for j,(oo,aa,bb) in enumerate(zip(*schema)):
  op=next(i for i,k in enumerate(oo) if k in model)
  a=next(i for i,k in enumerate(aa) if k in model)
  b=next(i for i,k in enumerate(bb) if k in model)
  if a==N+j:a=-1
  if b==N+j:b=-1
  gs.append((op,a,b))
 return gs
def evaluate(gs):
 ws=X.copy()
 for o,a,b in gs:
  va=0 if a<0 else ws[a];vb=0 if b<0 else ws[b]
  ws.append(va&vb if o==0 else va|vb if o==1 else MASK^va)
 return ws[-1]^TARGET
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--out',required=True);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--rounds',type=int,default=20);ap.add_argument('--gates',type=int,default=24);ap.add_argument('--fixed');ap.add_argument('--unlock');ap.add_argument('--samples');ap.add_argument('--cone',action='store_true');ap.add_argument('--ordered',action='store_true');ap.add_argument('--distinct',action='store_true');ap.add_argument('--not-count',type=int);ap.add_argument('--no-constants',action='store_true');ap.add_argument('--profile',choices=['default','sat','unsat'],default='default');a=ap.parse_args()
 out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
 samples=set(x for x in range(1<<N) if x.bit_count()<=2)
 if a.samples:samples.update(json.loads(Path(a.samples).read_text()))
 fixed=json.loads(Path(a.fixed).read_text())['gates'] if a.fixed else None
 unlocked=set(map(int,a.unlock.split(','))) if a.unlock else set()
 rng=random.Random(9811);started=time.monotonic()
 for r in range(a.rounds):
  print('round',r,'samples',len(samples),'elapsed',round(time.monotonic()-started,2),flush=True)
  cnf,schema=make(sorted(samples),a.gates,fixed,unlocked,a.cone,a.ordered,a.distinct,a.not_count,a.no_constants)
  path=out/f'round-{r:03d}.cnf';cnf.write(path)
  (out/f'round-{r:03d}-schema.json').write_text(json.dumps(schema))
  (out/f'round-{r:03d}-samples.json').write_text(json.dumps(sorted(samples)))
  print('CNF',cnf.n,'vars',len(cnf.clauses),'clauses',flush=True)
  del cnf
  log=out/f'round-{r:03d}.solver.log'
  with log.open('w') as f:p=subprocess.run([a.solver,'--'+a.profile,'-t',str(a.seconds),str(path)],stdout=f,stderr=subprocess.STDOUT)
  print('solver exit',p.returncode,'elapsed',round(time.monotonic()-started,2),flush=True)
  text=log.read_text()
  if p.returncode==20:
   print('UNSAT for this synthesis model and sample constraints; no Lean certificate yet',flush=True);return
  if p.returncode!=10:
   print('UNKNOWN or solver failure',flush=True);return
  model={int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
  gs=decode(model,schema);delta=evaluate(gs)
  errors=[x for x in range(1<<N) if delta>>x&1]
  d={'gates':gs,'errors':len(errors),'round':r}
  (out/f'round-{r:03d}-candidate.json').write_text(json.dumps(d))
  print('full truth-table errors',len(errors),flush=True)
  assert not any(x in samples for x in errors),'encoding error: candidate fails sample'
  if not errors:
   (out/'FOUND.json').write_text(json.dumps(d));print('FOUND',json.dumps(gs),flush=True);return
  samples.update(errors[:32]);samples.update(rng.sample(errors,min(32,len(errors))))
 print('round budget exhausted',flush=True)
if __name__=='__main__':main()
