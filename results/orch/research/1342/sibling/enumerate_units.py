from itertools import combinations, permutations, product
from pathlib import Path
import json
E = {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}
V=tuple(range(11))
deg={v:sum(v in e for e in E) for v in V}
parts=[tuple(v for v in V if deg[v]==d) for d in sorted(set(deg.values()))]
auts=[]
for parts_perm in product(*(list(permutations(p)) for p in parts)):
 a={v:w for p,q in zip(parts,parts_perm) for v,w in zip(p,q)}
 if {tuple(sorted((a[u],a[v]))) for u,v in E}==E:auts.append(tuple(a[v] for v in V))
def canonunit(A,B):return tuple(sorted((tuple(sorted(A)),tuple(sorted(B)))))
def canonorbit(A,B):return min(canonunit(tuple(g[a] for a in A),tuple(g[b] for b in B)) for g in auts)
def evalunit(A,B,S):return bool(set(A)&set(S)) and bool(set(B)&set(S))
units=[]
for A,B in combinations(tuple(combinations(V,2)),2):
 common=set(A)&set(B)
 if common:
  other=tuple(sorted(set(A)^set(B)))
  allowed=other in E
 else:
  allowed=any(evalunit(A,B,e) for e in E)
 if not allowed:continue
 accepted=[e for e in sorted(E) if evalunit(A,B,e)]
 false_pairs=[e for e in combinations(V,2) if e not in E and evalunit(A,B,e)]
 units.append({'A':A,'B':B,'overlap':len(common),'accepted_edges':accepted,'false_pairs':false_pairs,'orbit':canonorbit(A,B)})
reps={}
for u in units: reps.setdefault(u['orbit'],u)
summary={'degree_parts':parts,'automorphisms':auts,'nondegenerate_units_before_sieve':1485,'surviving_units':len(units),'surviving_orbits':len(reps),'disjoint_units':sum(u['overlap']==0 for u in units),'overlap_units':sum(u['overlap']==1 for u in units),'disjoint_orbits':sum(u['overlap']==0 for u in reps.values()),'overlap_orbits':sum(u['overlap']==1 for u in reps.values())}
out=Path('/tmp/oec/pequalnp-pilot-46/gap-1342/sibling')
(out/'unit-enumeration.json').write_text(json.dumps({'summary':summary,'representatives':list(reps.values()),'units':units},indent=2)+'\n')
print(json.dumps(summary,indent=2))
