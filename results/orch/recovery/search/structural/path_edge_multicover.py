from itertools import combinations
from time import monotonic
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N=[set() for _ in range(10)]
for a,b in E:N[a].add(b);N[b].add(a)
paths=[(a,c,b) for c in range(10) for a,b in combinations(sorted(N[c]),2)]
def comps(s,k):
 if k==1:yield(s,)
 else:
  for a in range(s+1):
   for b in comps(s-a,k-1):yield(a,)+b
for s in range(7,11):
 t=monotonic();sol=None;checked=0
 for xs in comps(s,10):
  checked+=1
  if all(xs[a]+xs[b]>=1 for a,b in E) and all(sum(xs[i] for i in p)>=2 for p in paths):sol=xs;break
 print('extras',s,'solution',sol,'checked',checked,'seconds',monotonic()-t,flush=True)
 if sol:break
