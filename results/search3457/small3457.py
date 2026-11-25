from itertools import combinations_with_replacement
from pathlib import Path
import json

N=2
n=2*N
inputs=tuple(sum(1<<a for a in range(1<<n) if (a>>i)&1) for i in range(n))
onehots=sum(1<<(1<<i) for i in range(n))
edge_masks={(p,l):inputs[p]&inputs[N+l] for p in range(N) for l in range(N)}
targets={}
for e in range(1<<(N*N)):
 if e==15:continue
 target=0
 nonedges=0
 for p in range(N):
  for l in range(N):
   if (e>>(p*N+l))&1:target|=edge_masks[p,l]
   else:nonedges|=1<<((1<<p)|(1<<(N+l)))
 targets[e]=(target,nonedges)

def solve(forbidden,maxdepth=4):
 states={frozenset(inputs)}
 minima={0:0,**{x:0 for x in inputs}}
 counts=[]
 wanted={v[0] for v in targets.values()}
 for depth in range(1,maxdepth+1):
  nxt=set()
  for s in states:
   for a,b in combinations_with_replacement(s,2):
    for op,v in [('or',a|b),('and',a&b)]:
     if v in s or v==0:continue
     if op=='and' and v&forbidden:continue
     minima.setdefault(v,depth)
     nxt.add(s|{v})
  counts.append(len(nxt));states=nxt
  if wanted.issubset(minima):break
 return minima,counts

dirty,counts=solve(onehots,3)
print('Dirty states per level',counts,flush=True)
answer=[]
for e,(target,nonedges) in targets.items():
 clean,cc=solve(onehots|nonedges,3)
 # All N=2 C4free graph targets have a canonical circuit of size at most four.
 dm=dirty.get(target,4);cm=clean.get(target,4)
 assert dm==cm,(e,dm,cm)
 answer.append({'incidence_mask':e,'dirty_min':dm,'clean_min':cm})
 print(answer[-1],flush=True)
Path('/tmp/oec/pequalnp-pilot-53/search/small3457.json').write_text(json.dumps(answer,indent=2)+'\n')
