from itertools import combinations,product
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def f(x):return any(x>>a&1 and x>>b&1 for a,b in E)
def fam(S):
 T=[i for i in range(10) if i not in S];F=set()
 for y in range(1<<len(T)):
  base=sum(((y>>j)&1)<<v for j,v in enumerate(T));tt=0
  for z in range(1<<len(S)):
   x=base|sum(((z>>j)&1)<<v for j,v in enumerate(S))
   tt|=int(f(x))<<z
  F.add(tt)
 return frozenset(F)
if __name__=='__main__':
 for k in [2,3,4,5]:
  groups={}
  for S in combinations(range(10),k):groups.setdefault(len(fam(S)),[]).append(S)
  print(k,[(n,len(x),x[:3]) for n,x in sorted(groups.items())],flush=True)
