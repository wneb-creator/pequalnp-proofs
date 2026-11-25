import random,time,json,sys
from pathlib import Path
N=14; S=24; M=(1<<(1<<N))-1
E=[(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
X=[sum(1<<j for j in range(1<<N) if j>>i&1) for i in range(N)]
T=0
for a,b in E:T|=X[a]&X[b]
PAIR=sum(1<<j for j in range(1<<N) if j.bit_count()<=2)
NEAR=sum(1<<j for j in range(1<<N) if j.bit_count()<=4)
print('truth zeros', (M^T).bit_count(), flush=True)
def seed(side):
 gates=[]; outs=[]
 for a in range(side*7,(side+1)*7):
  ns=[v if u==a else u for u,v in E if u==a or v==a]
  cur=ns[0]
  for b in ns[1:]:gates.append((1,cur,b));cur=N+len(gates)-1
  gates.append((0,a,cur));outs.append(N+len(gates)-1)
 cur=outs[0]
 for b in outs[1:]:gates.append((1,cur,b));cur=N+len(gates)-1
 return gates
def evaluate(gs):
 vs=X.copy()
 for op,a,b in gs:
  if op==0:vs.append(vs[a]&vs[b])
  elif op==1:vs.append(vs[a]|vs[b])
  else:vs.append(M^vs[a])
 d=vs[-1]^T
 return (d&PAIR).bit_count()*65536+d.bit_count()
def trim(gs,k,repl):
 ans=[]
 def adj(a):
  if a==N+k:a=repl
  return a-(a>N+k)
 for i,(op,a,b) in enumerate(gs):
  if i!=k:ans.append((op,adj(a),adj(b)))
 return ans
pool=[]
for side in range(2):
 gs=seed(side);assert len(gs)==25 and evaluate(gs)==0
 for k,(op,a,b) in enumerate(gs[:-1]):
  for r in [a,b]:pool.append(trim(gs,k,r))
print('seed best',min(map(evaluate,pool)),flush=True)
rng=random.Random(19811)
best=100000;total=0;start=time.monotonic();end=start+float(sys.argv[1] if len(sys.argv)>1 else 300)
while time.monotonic()<end:
 gs=rng.choice(pool).copy(); score=evaluate(gs)
 for iteration in range(30000):
  if time.monotonic()>=end:break
  new=gs.copy()
  nm=1 if rng.random()<.92 else rng.randrange(2,5)
  for _ in range(nm):
   i=rng.randrange(S);op,a,b=new[i]
   q=rng.randrange(5)
   if q==0:op=rng.randrange(3)
   elif q<3:a=rng.randrange(N+i)
   else:b=rng.randrange(N+i)
   new[i]=(op,a,b)
  ns=evaluate(new);total+=1
  if ns<=score:
   gs,score=new,ns
  if ns<best:
   best=ns
   print('best',best,'total',total,'seconds',round(time.monotonic()-start,1),flush=True)
   Path('/tmp/oec/pequalnp-pilot-85/counterexample/best-pair.json').write_text(json.dumps({'errors':best,'gates':new,'total':total,'seconds':time.monotonic()-start}))
  if ns==0:
   print('FOUND',json.dumps(new),flush=True);sys.exit(0)
print('done best',best,'total',total,'seconds',round(time.monotonic()-start,1),flush=True)
