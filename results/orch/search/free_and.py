import itertools,json,time
from functools import lru_cache

def run(n,m,E,max_or,cap):
 N=n+m;assign=[1<<i for i in range(N)]+[(1<<i)|(1<<j) for i,j in itertools.combinations(range(N),2)]
 inp=tuple(sum(1<<k for k,a in enumerate(assign) if (a>>i)&1) for i in range(N))
 edgepos=[assign.index((1<<a)|(1<<(n+b))) for a,b in E]
 good=sum(1<<k for k in edgepos);bad=((1<<len(assign))-1)^good
 relevant=good|((1<<N)-1)
 start=set(inp)
 start.update(a&b for a in inp for b in inp if (a&b)&relevant)
 @lru_cache(None)
 def score(cover):
  dp={0:0}
  for cm in cover:
   for s,c in list(dp.items()):
    t=s|cm
    if dp.get(t,999)>c+1:dp[t]=c+1
  return max(s.bit_count()-c for s,c in dp.items())
 states={tuple(sorted(start))};total=0;t0=time.time()
 for r in range(max_or+1):
  nxt=set()
  for idx,ws in enumerate(states):
   cover=set(w for w in ws if not w&bad)
   cover=tuple(sorted(c for c in cover if not any(c!=b and c|b==b for b in cover)))
   v=score(cover)
   if v>r:
    print('COUNTEREXAMPLE',json.dumps({'n':n,'m':m,'E':E,'or_count':r,'margin':v-r,'signals':ws,'assignments':assign,'cover':cover}),flush=True);return False
   if r==max_or:continue
   old=set(ws)
   for i,a in enumerate(ws):
    for b in ws[i+1:]:
     f=a|b
     if f in old:continue
     new=old|{f}|{f&g for g in ws if (f&g)&relevant}
     nxt.add(tuple(sorted(new)))
   if len(nxt)>cap:
    print(json.dumps({'event':'free_and_generation_cap','n':n,'m':m,'or_depth_complete':r-1,'or_depth_partial':r,'examined_at_partial_depth':idx+1,'states_at_partial_depth':len(states),'next_states_generated':len(nxt),'total_preceding_states':total,'elapsed':time.time()-t0}),flush=True);return True
  total+=len(states)
  print(json.dumps({'event':'free_and_depth','n':n,'m':m,'or_count':r,'states':len(states),'total':total,'next_states':len(nxt),'elapsed':time.time()-t0}),flush=True)
  states=nxt
 return True
if __name__=='__main__':
 for n,m,E in [(2,3,[(0,0),(0,1),(1,1),(1,2)]),(3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)])]:
  if not run(n,m,E,2,200000):break
