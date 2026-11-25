from pathlib import Path
import sys,itertools,random
sys.argv=['validate','2'];import fresh_meta3773_extended_model as m
import fresh_meta3773_five_search as r
import fresh_meta3773_k4_lowfan_fast as old
old.NP=m.NP;old.NT=m.NT
rng=random.Random(794005);cnt=0
for k in range(2,10):
 for j in range(12):
  F=tuple(sorted(rng.choices(m.raw,k=k)));p=m.target&rng.getrandbits(m.NT);n=(m.M^m.target)&rng.getrandbits(m.NT)
  assert m.feasible(F,p,n)==old.feasible_python(F,p,n);cnt+=1
print('extended 64-bit C++ recurrence compared to Python',cnt,'theta4 cases, including 17 negative test rows')
F=tuple(sorted(m.raw)); raw_s=set()
for s in range(1,(1<<len(F))-1):
 if s.bit_count()<2:continue
 S=tuple(x for i,x in enumerate(F)if s>>i&1);T=tuple(x for i,x in enumerate(F)if not s>>i&1);g1=set();g0=set()
 for p in range(m.NP):
  for q in range(m.NP,m.NT):
   if all(not(x>>p&1) or (x>>q&1) for x in T):g1.add(p);g0.add(q)
 if all(any((x>>p&1)and not(x>>q&1)for x in S)for p in g1 for q in g0):raw_s.add((S,T,sum(1<<p for p in g1),sum(1<<q for q in g0)))
assert not raw_s and not r.splits(F);print('theta4 no raw-token repeats: no earliest cone candidate, independent direct separation test')
# Build the direct ordinary five-star expression as a formula with repeated line leaf occurrences.
extra=[m.raw[l]for l in range(m.point_count,m.raw_count) for _ in range(sum(y==l for p,y in m.E)-1)]
assert m.feasible(tuple(sorted((*m.raw,*extra))),m.target,m.M^m.target); print('known 16-gate theta4 positive accepted; raw extra counts',len(extra))
