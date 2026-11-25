from functools import lru_cache
from itertools import combinations
from time import monotonic
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
TT=sum(1<<x for x in range(1024) if any(x>>a&1 and x>>b&1 for a,b in E))
@lru_cache(None)
def normalize(n,tt):
 if tt==0 or tt==(1<<(1<<n))-1:return (0, bool(tt))
 for i in range(n):
  lo=restrict(n,tt,i,0);hi=restrict(n,tt,i,1)
  if lo==hi:return normalize(n-1,lo)
 return n,tt
@lru_cache(None)
def restrict(n,tt,i,b):
 out=0
 for x in range(1<<(n-1)):
  j=(x&((1<<i)-1))|((x>>i)<<(i+1))|(b<<i)
  out|=((tt>>j)&1)<<x
 return out
@lru_cache(None)
def lower(n,tt):
 nn,ttn=normalize(n,tt)
 if nn!=n:return lower(nn,ttn)
 if n<2:return 0
 children=[[normalize(n-1,restrict(n,tt,i,b)) for b in [0,1]] for i in range(n)]
 costs=[[lower(*ch) for ch in row] for row in children]
 forced=[[c+(2 if ch[0] else 1) for c,ch in zip(rowc,row)] for rowc,row in zip(costs,children)]
 choices=[]
 for i in range(n):choices.append((max(forced[i]),('not',i)))
 for i,j in combinations(range(n),2):
  for ctrl in [0,1]:
   choices.append((max(forced[i][ctrl],forced[j][ctrl],1+costs[i][1-ctrl],1+costs[j][1-ctrl]),('and' if ctrl==0 else 'or',i,j)))
 best=min(choices)
 return max(n-1,best[0])
t0=monotonic()
print('lower',lower(10,TT), 'seconds',monotonic()-t0, 'cache',lower.cache_info(),flush=True)
for i in [0]:
 for b in [0,1]:
  ch=normalize(9,restrict(10,TT,i,b))
  print('cofactor',i,b,'vars',ch[0],'bound',lower(*ch),flush=True)
