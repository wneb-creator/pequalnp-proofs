from search import prepare,c4free
from functools import lru_cache
import itertools,json,random
rng=random.Random(53249)

def run(n,m,E,trials,maxg):
 inp,bad,evals,matching=prepare(n,m,E)
 @lru_cache(None)
 def cover_meet(v):
  return sum(1<<k for k,a in enumerate(evals) if (v>>a)&1)
 @lru_cache(None)
 def scores(cover):
  dp={0:0}
  for c in cover:
   for s,k in list(dp.items()):
    t=s|c
    if dp.get(t,999)>k+1:dp[t]=k+1
  return max(s.bit_count()-k for s,k in dp.items()),max(matching[s]-k for s,k in dp.items())
 best=[-100,-100]
 for t in range(trials):
  ws=list(inp);gs=[];ands=0
  for d in range(maxg):
   for tries in range(100):
    i=rng.randrange(len(ws));j=rng.randrange(len(ws));op=rng.randrange(2)
    v=ws[i]&ws[j] if op else ws[i]|ws[j]
    if v not in ws and v&bad:break
   else:break
   ws.append(v);gs.append((op,i,j));ands+=op
   cover=set()
   for i,u in enumerate(ws):
    for v in ws[i+1:]:
     meet=u&v
     if meet&bad:continue
     cm=cover_meet(meet)
     if cm:cover.add(cm)
   cover=tuple(sorted(c for c in cover if not any(c!=b and c|b==b for b in cover)))
   a,b=scores(cover);margins=[a-(d+1-ands),b-ands]
   for k in range(2):best[k]=max(best[k],margins[k])
   if max(margins)>0:
    print('COUNTEREXAMPLE',json.dumps({'n':n,'m':m,'edges':E,'gates':gs,'margins':margins}),flush=True);return False
 print(json.dumps({'event':'random_split_done','n':n,'m':m,'edges':E,'trials':trials,'maxg':maxg,'best_margins':best,'cover_families':scores.cache_info().currsize}),flush=True)
 return True

if __name__=='__main__':
 for n,m in [(4,4),(5,5),(6,6)]:
  E=[(p,l) for p in range(n) for l in range(m) if (p-l)%7 in {0,1,3}]
  assert c4free(E)
  if not run(n,m,E,10000,15):break
