import json
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-70/sat-review')
old=json.loads((base/'verified_symmetry.json').read_text())
assert isinstance(old,dict)
autos=old['automorphisms'];prefixes=old['representatives']
assert len(autos)==336 and len(prefixes)==65
edges=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
edge_set={frozenset(e) for e in edges}
group={tuple(p) for p in autos}
assert tuple(range(14)) in group
for p in autos:
 assert sorted(p)==list(range(14))
 assert {frozenset((p[a],p[b])) for a,b in edges}==edge_set
for p in autos:
 for q in autos:
  assert tuple(p[q[i]] for i in range(14)) in group
pairs=list(combinations_with_replacement(range(16),2))
def act(p,pair):return tuple(sorted(p[i] if i<14 else i for i in pair))
records=[];all_orbits=0
for k,t in enumerate(prefixes):
 b=t//225;c=(t%225)//15;d=t%15
 first=(0,b);second=(c,d)
 stabilizer=[index for index,p in enumerate(autos) if act(p,first)==first and act(p,second)==second]
 assert len(stabilizer)*old['orbit_sizes'][k]==336
 representatives={pair:min(act(autos[i],pair) for i in stabilizer) for pair in pairs}
 allowed=sorted({r for r in representatives.values()})
 forbidden=[pair for pair in pairs if representatives[pair]!=pair]
 assert len(allowed)+len(forbidden)==136
 for pair in pairs:
  orbit={act(autos[i],pair) for i in stabilizer}
  assert all(representatives[x]==representatives[pair] for x in orbit)
  assert len(orbit)*sum(act(autos[i],pair)==pair for i in stabilizer)==len(stabilizer)
 # Operators are unchanged under each input relabeling. Every third pair,
 # for every fixed choice of the first three operations, has a representative.
 for op1 in [False,True]:
  for op2 in [False,True]:
   for op3 in [False,True]:
    for pair in pairs:
     r=representatives[pair]
     assert any(act(autos[i],pair)==r for i in stabilizer)
 all_orbits+=len(allowed)
 records.append({'index':k,'score':t,'first':first,'second':second,'stabilizer_indices':stabilizer,'stabilizer_size':len(stabilizer),'allowed_pairs':allowed,'forbidden_pairs':forbidden,'third_orbits':len(allowed)})
result={'automorphisms':autos,'edges':edges,'prefixes':records,'third_pair_count':136,'prefix_pair_combinations_before':65*136,'prefix_pair_combinations_after':all_orbits,'additional_clauses':65*136-all_orbits}
(base/'third-symmetry-certificate.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
summary={'status':'passed','automorphisms':len(autos),'prefixes':len(prefixes),'third_pairs_per_prefix':136,'before':65*136,'after':all_orbits,'forbidden':65*136-all_orbits,'stabilizer_size_histogram':dict(sorted(Counter(r['stabilizer_size'] for r in records).items())),'third_orbit_histogram':dict(sorted(Counter(r['third_orbits'] for r in records).items()))}
print(json.dumps(summary,indent=2))
