from pathlib import Path
import sys,itertools,random,functools
sys.argv=['verify','0'];import fresh_meta3773_five_multiset as impl
import fresh_meta3773_k4_lowfan_fast as oracle
m=impl.model;r=impl.driver;rng=random.Random(792730); nchecked=0
# Independently permute the truth rows so the Python reference sees arbitrary
# internal-cone Boolean specifications, including 25 to 30 requested zeros.
for n in range(2,9):
 for j in range(32):
  F=tuple(sorted(rng.choices(m.raw+m.free,k=n)));P=m.M&rng.getrandbits(m.NT); P=(1<<(j%m.NT)) if j%3==0 else P;N=m.M^P
  order=[i for i in range(m.NT)if P>>i&1]+[i for i in range(m.NT)if N>>i&1];sz=P.bit_count(); oracle.NP=sz;oracle.NT=m.NT
  def reindex(x):return sum(1<<b for b,a in enumerate(order)if x>>a&1)
  assert impl.solve(F,P,N)==oracle.feasible_python(tuple(map(reindex,F)),(1<<sz)-1,m.M^((1<<sz)-1));nchecked+=1
print('arbitrary cone-specification tests passed',nchecked)
rawmask=(1<<m.raw_count)-1; negative=[x for x in range(rawmask+1)if not any(x>>i&1 and x>>j&1 for i,j in m.E)];maxneg={x for x in negative if all((x>>i&1)or(x|(1<<i)) not in negative for i in range(m.raw_count))};assert maxneg==set(m.N) and len(m.E)==14 and len(maxneg)==17
# All graph/OR inputs are independently inspected under the eight candidate point symmetries.
assert len(m.perms)==8; assert all({(p[i],p[j])for i,j in m.E}==set(m.E)and {frozenset(p[j]for j in S)for S in m.support}==set(map(frozenset,m.support)) for p in m.perms)
extra=[m.raw[l]for l in range(5,m.raw_count) for _ in range(sum(y==l for p,y in m.E)-1)];assert len(extra)==8 and impl.solve(tuple(sorted((*m.raw,*extra))),m.target,m.M^m.target)
print('independent maximal-negative generation and eight restricted feature automorphisms agree; 18-gate ordinary star positive control passes')
for t in range(75):
 R=rng.randrange(1<<m.raw_count);Cs=tuple(rng.randrange(1<<m.raw_count)for _ in range(rng.randrange(4)));h=rng.randrange(5)
 # Explicitly choose one carrier vertex per known branch without sharing that branch.
 choices=[[0]+[1<<i for i in range(m.raw_count)if C>>i&1]for C in Cs]
 oracle_result=any(any((U&~(R|functools.reduce(int.__or__,parts,0))).bit_count()<=h for U in r.covers)for parts in itertools.product(*choices))
 assert oracle_result==r.cover_ok(R,Cs,h)
print('75 independent explicit eligible-cover assignments match branch matching')
