from functools import lru_cache
from itertools import product
atoms=[sum(((r>>i)&1)<<r for r in range(8)) for i in range(3)]
required=frozenset([200,234,254])
full=frozenset([200,204,234,238,248,250,252,254,255])
@lru_cache(None)
def states(counts):
 total=sum(counts)
 if total==1:
  i=counts.index(1)
  return {frozenset([0,255,atoms[i]]),frozenset([0,255,atoms[i]^255])}
 result=set()
 for left in product(*(range(c+1) for c in counts)):
  if not 0<sum(left)<total:continue
  right=tuple(c-l for c,l in zip(counts,left))
  for A in states(tuple(left)):
   for B in states(right):
    result.add(frozenset([0,255]+[a&b for a in A for b in B]))
    result.add(frozenset([0,255]+[a|b for a in A for b in B]))
 return result
checked=0
for counts in product(range(3),repeat=3):
 if not 1<=sum(counts)<=4:continue
 ss=states(counts);checked+=len(ss)
 assert not any(required<=s for s in ss),(counts,'three-function obstruction failed')
 assert not any(full<=s for s in ss),(counts,'full cofactor family obstruction failed')
print('Independent enumeration verified:',checked,'distinct signatures across occurrence vectors; no ≤4-leaf signed skeleton covers {200,234,254}.')
for c in [(1,2,1),(1,1,2),(2,1,1)]:print('occurrence vector',c,'signatures',len(states(c)))
# The two-function claim would be wrong; this explicit skeleton is a regression check.
x,y,z=map(lambda a:frozenset([0,255,a]),atoms)
def combine(A,B,op):return frozenset([0,255]+[op(a,b) for a in A for b in B])
T=combine(combine(y,combine(x,z,lambda a,b:a|b),lambda a,b:a&b),y,lambda a,b:a|b)
assert {200,254}<=T
print('Confirmed two-function pruning counterexample; three cofactors are necessary for this certificate.')
