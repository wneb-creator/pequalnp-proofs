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
random.seed(500262510)
original=gates.copy(); ng=68

def make():
 gs=[]
 for j,(op,a,b) in enumerate(original):
  at=len(gs);gs.append((random.randrange(2),random.randrange(n+at),random.randrange(n+at)))
  gs.append((op,n+2*(a-n)+1 if a>=n else a,n+2*(b-n)+1 if b>=n else b))
 return gs,n+ng-1

def evaluate(gs,out):
 active=set();stack=[out]
 while stack:
  wire=stack.pop()
  if wire<n or wire in active:continue
  active.add(wire);_,a,b=gs[wire-n];stack.extend([a,b])
 vals=xs.copy()
 for j,(op,a,b) in enumerate(gs):
  vals.append((vals[a]&vals[b] if op else vals[a]|vals[b]) if n+j in active else 0)
 return (vals[out]^pm).bit_count(),len(active),active

start=time.monotonic();iters=0;best=1000;restarts=0
while time.monotonic()-start<300:
 cur,out=make();err,size,act=evaluate(cur,out);restarts+=1
 for it in range(500000):
  trial=cur.copy();tout=out
  for _ in range(1+(random.random()<.1)):
   if random.random()<.02:
    tout=random.randrange(n,n+ng)
   else:
    g=random.randrange(ng);o,a,b=trial[g];which=random.randrange(5)
    if which==0:o^=1
    elif which<3:a=random.randrange(n+g)
    else:b=random.randrange(n+g)
    trial[g]=(o,a,b)
  ee,ss,aa=evaluate(trial,tout);iters+=1
  cap=36 if it%20000<15000 else 34
  oldscore=err*10+max(size-cap,0)
  score=ee*10+max(ss-cap,0)
  if score<=oldscore:cur=trial;out=tout;err=ee;size=ss;act=aa
  if ee==0 and ss<best:
   best=ss;print(dict(best=best,time=time.monotonic()-start,iters=iters,restarts=restarts,gates=trial,out=tout),flush=True)
   if best<=33:
    print('FOUND',flush=True);sys.exit(0)
  if time.monotonic()-start>=300:break
print(dict(done=True,best=best,iters=iters,restarts=restarts,time=time.monotonic()-start),flush=True)
