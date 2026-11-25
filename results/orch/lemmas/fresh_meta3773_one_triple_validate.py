from pathlib import Path
import json,sys,itertools,random
sys.argv=['v','1']; import fresh_meta3773_five_wide as impl
import fresh_meta3773_k4_lowfan_fast as oracle
m=impl.model; d=impl.driver; rng=random.Random(37731);assert len(m.E)==17 and len(m.N)==24 and len(m.free)==7 and m.raw_count==13
G={frozenset(e)for e in m.E};ind={x for x in range(1<<m.raw_count) if not any(x>>a&1 and x>>b&1 for a,b in G)};assert {x for x in ind if all(x>>i&1 or (x|1<<i)not in ind for i in range(m.raw_count))}==set(m.N)
for p in m.perms:assert {frozenset(p[v] for v in e)for e in G}==G and {frozenset(p[v]for v in e)for e in m.support}==set(map(frozenset,m.support))
for mask in range(128):
 if mask.bit_count()<6:continue
 images=[]
 for p in m.perms:
  perm=[m.support.index({p[v] for v in e})for e in m.support];images.append(sum(1<<perm[i]for i in range(7)if mask>>i&1))
 if min(images)==mask:print('high-helper orbit representative',mask,mask.bit_count(),'orbit size',len(set(images)))
for n in range(2,9):
 for j in range(15):
  f=tuple(sorted(rng.choices(m.raw+m.free,k=n)));pos=(m.M&rng.getrandbits(m.NT)) if j%3==0 else 1<<j;neg=m.M^pos
  order=[i for i in range(m.NT)if pos>>i&1]+[i for i in range(m.NT)if neg>>i&1]; sp=pos.bit_count();oracle.NP=sp;oracle.NT=m.NT
  def reindex(x):return sum(1<<i for i,v in enumerate(order)if x>>v&1)
  assert impl.solve(f,pos,neg)==oracle.feasible_python(tuple(map(reindex,f)),(1<<sp)-1,m.M^((1<<sp)-1))
print('105 arbitrary cone specifications including 40 negative rows agree with independent labelled Python recurrence')
print('representative',m.data['points'],'edge rows',len(m.E),'maximal negatives',len(m.N),'raw',len(m.raw),'helpers',len(m.free),'symmetries',len(m.perms))
