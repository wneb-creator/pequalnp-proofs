from search import prepare,c4free
import itertools,json,time
from functools import lru_cache

def run(n,m,edges,maxd):
 inputs,bad,evals,matching=prepare(n,m,edges); q=len(edges)
 @lru_cache(None)
 def joint(u,v):
  meet=u&v
  if meet&bad:return 0
  return sum(1<<k for k,a in enumerate(evals) if (meet>>a)&1)
 @lru_cache(None)
 def val(cover):
  dp={0:0}
  for cm in cover:
   for s,c in list(dp.items()):
    t=s|cm
    if dp.get(t,999)>c+1:dp[t]=c+1
  return max(s.bit_count()+matching[s]-2*c for s,c in dp.items())
 states={inputs};total=0
 for d in range(maxd+1):
  nxt=set()
  for ws in states:
   covers=set()
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     cm=joint(min(u,v),max(u,v))
     if cm:covers.add(cm)
   covers=tuple(sorted(c for c in covers if not any(c!=b and c|b==b for b in covers)))
   margin=val(covers)-d
   if margin>0:
    print('COUNTEREXAMPLE',json.dumps({'n':n,'m':m,'edges':edges,'ws':ws,'depth':d,'margin':margin}),flush=True)
    return False
   if d==maxd:continue
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     for w in [u&v,u|v]:
      if w in ws or not w&bad:continue
      nxt.add(tuple(sorted(ws+(w,))))
  total+=len(states)
  print(json.dumps({'event':'exhaustive_depth','n':n,'m':m,'edges':edges,'depth':d,'states':len(states),'total':total,'distinct_cover_families':val.cache_info().currsize}),flush=True)
  states=nxt
 return True

if __name__=='__main__':
 cases=[(2,3,[(0,0),(0,1),(1,1),(1,2)]),(3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]),(3,4,[(0,0),(0,1),(0,3),(1,1),(1,2),(2,2),(2,0)])]
 for n,m,E in cases:
  if not run(n,m,E,3):break
