from itertools import combinations
from datetime import datetime, timezone
import json
N=2
n=2*N
R=1<<n
inp=tuple(sum(1<<r for r in range(R) if r>>i&1) for i in range(n))
single=sum(1<<(1<<i) for i in range(n))
allcross=sum(1<<((1<<i)|(1<<(N+j))) for i in range(N) for j in range(N))
targets={}
for E in range(1<<(N*N)):
 if E==(1<<(N*N))-1: continue
 edges=[(i,N+j) for i in range(N) for j in range(N) if E>>(i*N+j)&1]
 t=sum(1<<r for r in range(R) if any((r>>i&1) and (r>>j&1) for i,j in edges))
 good=sum(1<<((1<<i)|(1<<j)) for i,j in edges)
 targets[E]=(t,single|(allcross^good))
regular={0:0}; clean={0:0}
# state maps available functions to an antichain of minimal masks of forbidden AND assignments
states={tuple(sorted(inp)):{0}}
counts=[]
for depth in range(1,6):
 nxt={}
 for funcs,masks in states.items():
  existing=set(funcs)
  for a,b in combinations(funcs,2):
   for op,c in [(0,a&b),(1,a|b)]:
    if c in existing: continue
    fs=tuple(sorted((*funcs,c)))
    bad=(c&(single|allcross)) if op==0 else 0
    ms=nxt.setdefault(fs,set())
    for m in masks:
     q=m|bad
     if any(x&q==x for x in ms): continue
     ms.difference_update([x for x in ms if x&q==q]); ms.add(q)
     for e,(t,fbd) in targets.items():
      if c==t:
       regular.setdefault(e,depth)
       if not (q&fbd): clean.setdefault(e,depth)
 states=nxt
 counts.append((depth,len(states),sum(map(len,states.values()))))
 print(datetime.now(timezone.utc).isoformat(),counts[-1],regular,clean,flush=True)
 if len(clean)==len(targets): break
out={'N':N,'states_by_depth':counts,'regular_minimum':regular,'clean_minimum':clean,'all_equal':regular==clean,'covered':len(clean),'target_count':len(targets)}
print(json.dumps(out,sort_keys=True),flush=True)
