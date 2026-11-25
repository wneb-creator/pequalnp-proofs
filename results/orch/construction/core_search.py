import time,random,json,sys
D={0,1,3,9}; S=sorted(D|{(x+1)%13 for x in D}); inp=S+list(range(13,26)); n=len(inp)
reps=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
neg=set()
for p,w in reps:
 for m in [1,3,9]:
  for t in range(13):
   for dual in [False,True]:
    mask=0
    for j,i in enumerate(inp):
     side=i>=13; ix=i%13; at=(m*ix+t)%13; at=(-at)%13 if dual else at
     v=(w if side^dual else p)>>at&1
     mask|=v<<j
    neg.add(mask)
pos={1<<inp.index(p)|1<<inp.index(13+w) for p in S for w in range(13) if (p-w)%13 in D}
assert not(pos&neg)
rows=sorted(pos)+sorted(neg); nm=len(rows); pm=(1<<len(pos))-1; allmask=(1<<nm)-1
xs=[sum(((x>>i)&1)<<t for t,x in enumerate(rows)) for i in range(n)]
gates=[];out=[]
def emit(op,a,b):
 gates.append((op,a,b));return n+len(gates)-1
for p in S:
 ns=[inp.index(13+w) for w in range(13) if (p-w)%13 in D]
 v=ns[0]
 for a in ns[1:]:v=emit(0,v,a)
 out.append(emit(1,inp.index(p),v))
v=out[0]
for a in out[1:]:v=emit(0,v,a)
assert len(gates)==34
print(dict(points=S,inputs=inp,positive=len(pos),negative=len(neg)),flush=True)
random.seed(5002625)
def evaluate(gs):
 vs=xs.copy()
 for op,a,b in gs: vs.append(vs[a]&vs[b] if op else vs[a]|vs[b])
 z=vs[-1]^pm
 return (z&pm).bit_count()*3+(z&~pm).bit_count()
def seed():
 cut=random.randrange(34); old=gates[cut]; replacement=random.choice(old[1:]); gs=[]
 for j,(o,a,b) in enumerate(gates):
  if j==cut:continue
  if a==n+cut:a=replacement
  if b==n+cut:b=replacement
  a-=int(a>n+cut);b-=int(b>n+cut)
  gs.append((o,a,b))
 return gs
start=time.monotonic();best=10000;iters=0;restarts=0
while time.monotonic()-start<240:
 cur=seed();score=evaluate(cur);stale=0;restarts+=1
 for it in range(20000):
  trial=cur.copy()
  for _ in range(1+(random.random()<.12)):
   g=random.randrange(33);o,a,b=trial[g];which=random.randrange(5)
   if which==0:o^=1
   elif which<3:a=random.randrange(n+g)
   else:b=random.randrange(n+g)
   trial[g]=(o,a,b)
  sc=evaluate(trial);iters+=1
  if sc<=score:cur=trial;score=sc
  if sc<best:
   best=sc;print(dict(best=best,time=time.monotonic()-start,iters=iters,restarts=restarts,gates=trial),flush=True)
  if sc==0:
   print('FOUND',json.dumps(trial),flush=True);sys.exit(0)
  if time.monotonic()-start>=240:break
print(dict(done=True,best=best,iters=iters,restarts=restarts,time=time.monotonic()-start),flush=True)
