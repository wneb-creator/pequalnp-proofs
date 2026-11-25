from itertools import combinations,product
from pathlib import Path
from time import monotonic
import json
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
pv=[e for e in edges if 0 not in e]
mask=(1<<1024)-1
raw=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
raw.append(mask^raw[0])
target=0
for a,b in edges:target |= raw[a]&raw[b]
base=Path('/tmp/oec/pequalnp-pilot-152/gap-1884')
start=monotonic();variants=0;tested=0

def planlist(gs):
 uses={}
 for i,(op,a,b) in enumerate(gs):
  for k,w in enumerate([a,b]):uses.setdefault(w,[]).append((i,k))
 plans=[]
 for w,pos in uses.items():
  for m in range(1,1<<len(pos)):
   chosen=frozenset(pos[j] for j in range(len(pos)) if m>>j&1)
   plans.append((w,chosen))
 return plans

def test(gs,po,pa):
 vals=raw[:];wo,so=po;wa,sa=pa
 if so&sa:return False
 for i,(op,a,b) in enumerate(gs):
  v=[]
  for k,w in enumerate([a,b]):
   x=vals[w]
   if (i,k) in so:x |= raw[0]
   if (i,k) in sa:x &= raw[10]
   v.append(x)
  vals.append(v[0]&v[1] if op=='and' else v[0]|v[1])
 return vals[-1]==target

for cover in combinations(range(1,10),5):
 S=set(cover)
 if any(a not in S and b not in S for a,b in pv):continue
 options=[[v for v in e if v in S] for e in pv]
 for owners in product(*options):
  gs=[];tops=[]
  def add(op,a,b):
   gs.append((op,a,b));return 10+len(gs)
  for c in cover:
   ns=[b if a==c else a for (a,b),owner in zip(pv,owners) if owner==c]
   if not ns:break
   u=ns[0]
   for v in ns[1:]:u=add('or',u,v)
   tops.append(add('and',c,u))
  else:
   out=tops[0]
   for t in tops[1:]:out=add('or',out,t)
   assert len(gs)==16
   variants+=1;plans=planlist(gs)
   for po in plans:
    for pa in plans:
     tested+=1
     if test(gs,po,pa):
      data={'gates':gs,'or_plan':[po[0],list(po[1])],'and_plan':[pa[0],list(pa[1])],'cover':cover,'owners':owners}
      (base/'mask-insertion-found.json').write_text(json.dumps(data,indent=2))
      print('FOUND exact full1024 candidate',data,flush=True);raise SystemExit(0)
   if variants%20==0:print('variants',variants,'tested',tested,'seconds',round(monotonic()-start,3),flush=True)
   if monotonic()-start>180:
    print('TIME LIMIT; restricted search incomplete',variants,tested,flush=True);raise SystemExit(0)
print('NO CANDIDATE in restricted canonical Pv16 formulas',variants,tested,'seconds',round(monotonic()-start,3),flush=True)
