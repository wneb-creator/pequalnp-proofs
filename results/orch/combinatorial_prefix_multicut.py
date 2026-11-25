from itertools import combinations
from collections import Counter
import json,time
N=10; M=(1<<(1<<N))-1
X=[sum(1<<a for a in range(1<<N) if a>>i&1) for i in range(N)]
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
T=0
for a,b in E:T|=X[a]&X[b]
ZERO=[a for a in range(1<<N) if not (T>>a&1)]
CUTS=json.loads(open("/tmp/oec/pequalnp-pilot-104/certificates/zero-cuts.json").read())
D=[]
for cut in CUTS:
 d=M
 for i in cut["removed"]: d &= M^X[i]
 D.append(d)
LB=[c["lower"] for c in CUTS]
BASE=[{x&d for x in X}|{(M^x)&d for x in X}|{0,d} for d in D]
def bins(a,b):return [a&b,a|b,a&(M^b),(M^a)&b]
def separates(ws):
 for r in ZERO:
  hit=T
  for w in ws:
   hit &= w if (w>>r)&1 else M^w
   if not hit:break
  if hit:return False
 return True
def restricted_cut(ws,prefix,k):
 for i,d in enumerate(D):
  bank=set(BASE[i]);cost=0
  for z in prefix:
   t=z&d
   if t not in bank:
    cost+=1;bank.add(t);bank.add(d^t)
  const=sum((w&d) in (0,d) for w in ws)
  if k+cost<LB[i]+const:return i,cost,const
 return None
def expand(ws,prefix,k):
 stats=Counter();out={}
 for a,b in combinations(ws,2):
  for z in bins(a,b):
   if z in ws or z in (0,M):continue
   rest=tuple(w for w in ws if w!=a and w!=b)
   for ka,kb in [(0,0),(0,1),(1,0),(1,1)]:
    state=tuple(sorted(rest+(a,)*ka+(b,)*kb+(z,)))
    stats['children']+=1
    if len(state)>k+1:stats['length']+=1;continue
    cut=restricted_cut(state,prefix+(z,),k)
    if cut:stats['restriction']+=1;continue
    if not separates(state):stats['separation']+=1;continue
    if state not in out:out[state]=prefix+(z,)
 stats['open_unique']=len(out)
 return stats,out

AUTOS=json.loads(open('/workspace/pequalnp-proofs/results/orch/few_nots_automorphisms.json').read())
def swaplist(p):
 cur=list(range(N));ops=[]
 for i in range(N):
  if cur[i]!=p[i]:
   a,b=sorted((cur[i],p[i]));d=(1<<b)-(1<<a)
   ma=X[a]&(M^X[b]);mb=X[b]&(M^X[a]);keep=M^(ma|mb)
   ops.append((d,ma,mb,keep))
   cur=[b if j==a else a if j==b else j for j in cur]
 return ops
def transformed(w,ops):
 for d,ma,mb,keep in ops:w=((w&ma)<<d)|((w&mb)>>d)|(w&keep)
 return w
start=time.time()
for pair in [(0,1),(0,2)]:
 auto=[p for p in AUTOS if {p[pair[0]],p[pair[1]]}==set(pair)]
 ops=[swaplist(p) for p in auto]
 for p,o in zip(auto,ops):
  assert transformed(T,o)==T
  assert all(transformed(x,o)==X[p[i]] for i,x in enumerate(X))
 trcache={}
 def canon(ws,prefix):
  for w in ws+prefix:
   if w not in trcache:trcache[w]=tuple(transformed(w,o) for o in ops)
  best=min(range(len(ops)),key=lambda j:tuple(sorted(trcache[w][j] for w in ws)))
  return tuple(sorted(trcache[w][best] for w in ws)),tuple(trcache[w][best] for w in prefix)
 z=X[pair[0]]|X[pair[1]]
 current={tuple(sorted(X+[z])):(z,)}
 for depth in range(2,5):
  total=Counter();nxt={};processed=0
  for ws,prefix in current.items():
   st,out=expand(ws,prefix,17-depth);total+=st;processed+=1
   for w,p in out.items():
    key,pr=canon(w,p);nxt.setdefault(key,pr)
   if len(nxt)>100000 or time.time()-start>240:break
  open('/tmp/oec/pequalnp-pilot-104/certificates/multicut-%s-%s-depth%s.json' % (*pair,depth),'w').write(json.dumps([[list(w),list(p)] for w,p in nxt.items()]))
  total.update({'states':len(nxt),'depth':depth,'cap':17,'parents_processed':processed,'parents_total':len(current),'stabilizer':len(auto)})
  print(json.dumps({'pair':pair,**dict(total)}),flush=True)
  current=nxt
  if len(current)>100000 or time.time()-start>240:break
print(json.dumps({'elapsed_seconds':time.time()-start}),flush=True)
