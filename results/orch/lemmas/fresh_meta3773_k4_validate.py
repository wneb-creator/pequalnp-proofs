from pathlib import Path
from itertools import combinations
import random,functools,subprocess
import fresh_meta3773_k4_lowfan_fast as m
import fresh_meta3773_k4_recursive as r
rng=random.Random(793773); count=0
for k in range(2,9):
 for t in range(15):
  fs=tuple(sorted(rng.choices(m.base,k=k)));p=m.target&rng.getrandbits(m.NT);q=(m.target^m.M)&rng.getrandbits(m.NT)
  assert m.feasible_python(fs,p,q)==m.feasible(fs,p,q);count+=1
print('Python/C++ read-once semantic recurrence comparisons',count)
for k in (1,2,3):
 F=tuple(sorted(m.raw+m.free[:k])); p=m.factorizations(F); a={(tuple(F[i]for i in range(len(F))if s>>i&1),tuple(F[i]for i in range(len(F))if t>>i&1),x,y) for s,t,x,y in p}; reduced=r.splits(F)
 assert set(reduced)<=a
 for A,B,p,n in a:
  if not any(tuple(sorted(r.images(v)[j] for v in A))==RA and tuple(sorted(r.images(v)[j]for v in B))==RB and r.images(p)[j]==rp and r.images(n)[j]==rn for RA,RB,rp,rn in reduced for j in range(24)):
   raise RuntimeError('unrepresented factorization')
 print('all Python cone split candidates represented by C++/S4',k,len(a),len(reduced))
assert m.feasible(tuple(sorted(m.raw+m.raw[4:])),m.target,m.M^m.target)
print('positive control: ordinary 15-gate star cover is a 16-leaf read-once formula after its six repeated edge-line slots are added')
# A correspondence with the same 12 positive/16 negative partition, constructed from F=(st+u)v+(st+w)z.
def target(row):
 s,t,u,v,w,z=[bool(row>>i&1)for i in range(6)];return ((s and t or u)and v)or((s and t or w)and z)
P=[x for x in range(64) if target(x) and all(not target(x^(1<<j)) for j in range(6)if x>>j&1)];N=[x for x in range(64)if not target(x) and all(target(x|(1<<j)) for j in range(6)if not(x>>j&1))]; assert len(P)<=12 and len(N)<=16
examples=[P[i%len(P)]for i in range(12)]+[N[i%len(N)]for i in range(16)];F=tuple(sorted(sum(1<<i for i,x in enumerate(examples)if x>>j&1) for j in range(6)));assert not m.feasible(F,m.target,m.M^m.target);assert r.search(r.canon(F),1)
print('positive control: six-variable function (st+u)v+(st+w)z requires a repeated occurrence and is recognized via shared cone search')
