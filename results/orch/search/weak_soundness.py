from search import prepare
import json,itertools
from functools import lru_cache

def run(n,m,edges,maxd,keep_dirty=True):
 inputs,bad,evals,matching=prepare(n,m,edges);q=len(edges)
 small=sum(1<<a for a in range(1<<(n+m)) if a.bit_count()<=2)
 weakbad=bad&small
 @lru_cache(None)
 def joint(u,v):
  meet=u&v
  if meet&weakbad:return 0
  return sum(1<<k for k,a in enumerate(evals) if (meet>>a)&1)
 @lru_cache(None)
 def val(cover):
  dp={0:0}
  for cm in cover:
   for s,c in list(dp.items()):
    t=s|cm
    if dp.get(t,999)>c+1:dp[t]=c+1
  return max(s.bit_count()-c for s,c in dp.items()),max(matching[s]-c for s,c in dp.items())
 states={(inputs,0)};total=0
 for d in range(maxd+1):
  nxt=set()
  for ws,na in states:
   covers=set()
   for i,u in enumerate(ws):
    for v in ws[i:]:
     cm=joint(min(u,v),max(u,v))
     if cm:covers.add(cm)
   covers=tuple(sorted(c for c in covers if not any(c!=b and c|b==b for b in covers)))
   e_val,m_val=val(covers)
   if e_val>d-na:
    print('COUNTEREXAMPLE',json.dumps({'n':n,'m':m,'edges':edges,'ws':ws,'depth':d,'ands':na,'edge_margin':e_val-(d-na),'matching_margin':m_val-na,'cover':covers,'keep_dirty':keep_dirty}),flush=True)
    return False
   if d==maxd:continue
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     for op,w in [(1,u&v),(0,u|v)]:
      if w in ws or not w:continue
      if keep_dirty and not w&bad:continue
      nxt.add((tuple(sorted(ws+(w,))),na+op))
  total+=len(states)
  print(json.dumps({'event':'weak_soundness_depth','n':n,'m':m,'edges':edges,'depth':d,'states':len(states),'total':total,'distinct_cover_families':val.cache_info().currsize,'keep_dirty':keep_dirty}),flush=True)
  states=nxt
 return True

if __name__=='__main__':
 cases=[(2,3,[(0,0),(0,1),(1,1),(1,2)]),(3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)])]
 for keep in [True,False]:
  for n,m,E in cases:
   if not run(n,m,E,4,keep):raise SystemExit(0)
