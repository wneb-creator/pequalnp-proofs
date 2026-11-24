from search import prepare
import json
from functools import lru_cache

def run(n,m,edges,maxd):
 inputs,bad,evals,matching=prepare(n,m,edges);q=len(edges)
 matchings=tuple(s for s in range(1,1<<q) if matching[s]==s.bit_count())
 @lru_cache(None)
 def emask(f):return sum(1<<k for k,a in enumerate(evals) if (f>>a)&1)
 @lru_cache(None)
 def joint(u,v):
  meet=u&v
  return 0 if meet&bad else emask(meet)
 @lru_cache(None)
 def mincovers(cover):
  dp={0:0}
  for cm in cover:
   for s,c in list(dp.items()):
    t=s|cm
    if dp.get(t,999)>c+1:dp[t]=c+1
  return tuple(min((c for t,c in dp.items() if s&t==s),default=999) for s in matchings)
 @lru_cache(None)
 def check(cover,ands):
  for s,cost in zip(matchings,mincovers(cover)):
   active=sum(bool(s&a) for a in ands)
   if s.bit_count()>active+cost:return s,active,cost
  return None
 states={(inputs,())};total=0
 for d in range(maxd+1):
  nxt=set()
  for ws,ands in states:
   covers=set()
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     cm=joint(min(u,v),max(u,v))
     if cm:covers.add(cm)
   cover=tuple(sorted(c for c in covers if not any(c!=b and c|b==b for b in covers)))
   failure=check(cover,tuple(sorted(emask(f) for f in ands)))
   if failure:
    print('COUNTEREXAMPLE',json.dumps({'n':n,'m':m,'edges':edges,'ws':ws,'and_functions':ands,'depth':d,'failure':failure,'cover':cover}),flush=True)
    return False
   if d==maxd:continue
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     for op,w in [(1,u&v),(0,u|v)]:
      if w in ws or not w&bad:continue
      nxt.add((tuple(sorted(ws+(w,))),tuple(sorted(ands+(w,))) if op else ands))
  total+=len(states)
  print(json.dumps({'event':'hall_depth','n':n,'m':m,'edges':edges,'depth':d,'states':len(states),'total':total,'resource_patterns':check.cache_info().currsize,'matchings':len(matchings)}),flush=True)
  states=nxt
 return True
if __name__=='__main__':
 cases=[(2,3,[(0,0),(0,1),(1,1),(1,2)]),(3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]),(3,4,[(0,0),(0,1),(0,3),(1,1),(1,2),(2,2),(2,0)])]
 for n,m,E in cases:
  if not run(n,m,E,4):break
