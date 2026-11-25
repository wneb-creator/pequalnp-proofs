from functools import lru_cache
from pathlib import Path
import json,time
E=[(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
es={tuple(sorted(e)):i for i,e in enumerate(E)}
bc=[]
for a in range(1,128):
 for b in range(a+1,128):
  if a&b:continue
  pairs=[tuple(sorted((u,v))) for u in range(7) if a>>u&1 for v in range(7) if b>>v&1]
  if all(e in es for e in pairs):bc.append((sum(1<<es[e] for e in pairs),a,b))
full=(1<<len(E))-1
contain=[[i for i,(m,a,b) in enumerate(bc) if m>>e&1] for e in range(len(E))]
@lru_cache(None)
def orcost(req):
 if not req:return (0,())
 m=max(req,key=int.bit_count)
 rest=set(req)-{m}; result=(999,())
 low=m&-m
 a=(m-1)&m
 while a:
  b=m^a
  if b and a&low:
   sub=tuple(sorted(rest|{x for x in (a,b) if x.bit_count()>1}))
   v,tr=orcost(sub)
   if v+1<result[0]:result=(v+1,((m,a,b),)+tr)
  a=(a-1)&m
 return result
seen=set(); best=15;best_data=None;nodes=0;started=time.time()
def dfs(mask,factors,chosen):
 global best,best_data,nodes
 nodes+=1
 k=len(chosen)
 if 2*k-1+len(factors)>=best:return
 state=(mask,factors,k)
 if state in seen:return
 seen.add(state)
 if mask==full:
  v,tr=orcost(factors);cost=2*k-1+v
  if cost<best:
   best=cost;best_data=[chosen,tr]
   print('BEST',cost,'COVER',[bc[i] for i in chosen],'OR',tr,'nodes',nodes,'time',time.time()-started,flush=True)
   Path('/tmp/oec/pequalnp-pilot-184/search/best-cover.json').write_text(json.dumps({'cost':cost,'cover':[bc[i] for i in chosen],'or':tr},indent=2))
  return
 if 2*(k+1)-1+len(factors)>=best:return
 missing=[e for e in range(len(E)) if not mask>>e&1]
 e=min(missing,key=lambda e:len(contain[e]))
 opts=sorted(contain[e],key=lambda i:-(bc[i][0]&~mask).bit_count())
 for i in opts:
  m,a,b=bc[i]
  fs=tuple(sorted(set(factors)|{x for x in (a,b) if x.bit_count()>1}))
  dfs(mask|m,fs,chosen+(i,))
dfs(0,(),())
print('DONE',best,best_data,'nodes',nodes,'states',len(seen),'orcache',orcost.cache_info(),'time',time.time()-started,flush=True)
