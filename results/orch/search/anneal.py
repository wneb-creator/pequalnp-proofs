import argparse,itertools,json,math,random,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('graph');p.add_argument('--seconds',type=int,default=600);p.add_argument('--out');a=p.parse_args()
g=json.loads(Path(a.graph).read_text());n=g['n'];es=[tuple(p) for p in g['edges']]
independent=lambda x: not any((x>>i&1) and (x>>j&1) for i,j in es)
neg=[x for x in range(1<<n) if independent(x) and all(not independent(x|(1<<i)) for i in range(n) if not(x>>i&1))]
pos=[(1<<i)|(1<<j) for i,j in es];rows=pos+neg;target=(1<<len(pos))-1
inputs=[sum((1<<k) for k,x in enumerate(rows) if x>>i&1) for i in range(n)]
covers=[]
for r in range(n+1):
 covers=[s for s in itertools.combinations(range(n),r) if all(i in s or j in s for i,j in es)]
 if covers:break
k=len(es)+r-2
rng=random.Random(731)
def evaluate(gs):
 ws=inputs.copy()
 for op,i,j in gs:ws.append((ws[i]|ws[j]) if op else (ws[i]&ws[j]))
 delta=ws[-1]^target
 return (delta&target).bit_count()*2+(delta&~target).bit_count(),ws[-1]
def start():
 cv=list(rng.choice(covers));rng.shuffle(cv);assigned={v:[] for v in cv}
 for i,j in es:
  opts=[v for v in (i,j) if v in assigned];v=rng.choice(opts);assigned[v].append(j if v==i else i)
 if any(not ns for ns in assigned.values()):return start()
 gs=[];outs=[]
 def gate(op,i,j):gs.append((op,i,j));return n+len(gs)-1
 for v,ns in assigned.items():
  rng.shuffle(ns);w=ns[0]
  for u in ns[1:]:w=gate(1,w,u)
  outs.append(gate(0,v,w))
 rng.shuffle(outs);w=outs[0]
 for u in outs[1:]:w=gate(1,w,u)
 assert evaluate(gs)[0]==0
 rem=rng.randrange(len(gs));wire=n+rem;replacement=rng.choice(gs[rem][1:]);gs.pop(rem)
 def fix(v):return replacement if v==wire else v-1 if v>wire else v
 gs=[(o,fix(i),fix(j)) for o,i,j in gs]
 return gs
best=1000;trials=0;restarts=0;started=time.time();deadline=started+a.seconds
while time.time()<deadline:
 gs=start();score,_=evaluate(gs);restarts+=1
 for step in range(100000):
  z=rng.randrange(k);old=gs[z];op,i,j=old;m=rng.randrange(8)
  if m<3:i=rng.randrange(n+z)
  elif m<6:j=rng.randrange(n+z)
  elif m==6:op=1-op
  else:i,j=rng.randrange(n+z),rng.randrange(n+z)
  gs[z]=(op,i,j);new,out=evaluate(gs);trials+=1
  temp=1.8*(1-(step%20000)/20000)+0.08
  if new<=score or rng.random()<math.exp((score-new)/temp):score=new
  else:gs[z]=old
  if score<best:
   best=score;record={'score':score,'n':n,'edges':es,'tau':r,'gates':gs,'trials':trials,'seconds':time.time()-started}
   Path(a.out).write_text(json.dumps(record,indent=2));print('best',best,'trials',trials,'seconds',round(time.time()-started,2),flush=True)
   if score==0:
    for x in range(1<<n):
     ws=[bool(x>>i&1) for i in range(n)]
     for op,i,j in gs:ws.append((ws[i] or ws[j]) if op else (ws[i] and ws[j]))
     assert ws[-1]==(not independent(x))
    print('VERIFIED FULL TRUTH TABLE',flush=True);raise SystemExit
  if trials%2000==0 and time.time()>=deadline:break
print('finished',{'best':best,'trials':trials,'restarts':restarts,'seconds':time.time()-started},flush=True)
