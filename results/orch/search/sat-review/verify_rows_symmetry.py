from itertools import combinations, permutations
import json
from pathlib import Path

edges=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
edge_set={frozenset(e) for e in edges}
neighbors={b:frozenset(a for a,c in edges if c==b) for b in range(7,14)}
line_id={v:k for k,v in neighbors.items()}
def third(a,b):
    return next(next(iter(S-{a,b})) for S in neighbors.values() if {a,b}<=S)
autos=[]
for a,b,c in permutations(range(7),3):
    if third(a,b)==c: continue
    p=[a,b,c,third(a,b),third(b,c),third(c,third(a,b)),third(a,c)]
    p += [line_id[frozenset(p[x] for x in neighbors[k])] for k in range(7,14)]
    assert {frozenset((p[a],p[b])) for a,b in edges}==edge_set
    autos.append(p)
pvec=[1,2,4,3,6,7,5]
lvec=[4,2,5,6,7,3,1]
dual=[7+lvec.index(v) for v in pvec]+[pvec.index(v) for v in lvec]
assert {frozenset((dual[a],dual[b])) for a,b in edges}==edge_set
autos += [[dual[v] for v in p] for p in autos[:]]
assert len({tuple(p) for p in autos})==336
canon=[226,227,228,232,233,234,236,239,258,259,260,262,263,264,266,267,269,277,278,281,284,338,341,344,354,355,356,359,402,404,1576,1577,1582,1583,1584,1589,1592,1593,1598,1599,1601,1604,1609,1611,1614,1617,1619,2026,2027,2032,2034,2036,2039,2042,2043,2045,2047,2048,2051,2053,2054,2058,2066,2067,2069]
def score(a,b,c,d):
    a,b=sorted((a,b));c,d=sorted((c,d));return (15*a+b)*225+15*c+d
remaining={score(a,b,c,d) for a,b in combinations(range(14),2) for c,d in combinations(range(15),2)}
representatives=[]
orbit_sizes=[]
while remaining:
    t=min(remaining);q,r=divmod(t,225);a,b=divmod(q,15);c,d=divmod(r,15)
    orbit={score(p[a],p[b],p[c] if c<14 else 14,p[d] if d<14 else 14) for p in autos}
    assert orbit<=remaining
    representatives.append(min(orbit));orbit_sizes.append(len(orbit));remaining-=orbit
assert representatives==canon
w=[95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
packed_rows=[sum(((v>>r)&1)<<i for i,v in enumerate(w)) for r in range(58)]
def target(m):return any((m>>a)&(m>>b)&1 for a,b in edges)
true_rows=[(1<<a)|(1<<b) for a,b in edges]
false_rows=[m for m in range(1<<14) if not target(m) and all(target(m|(1<<i)) for i in range(14) if not ((m>>i)&1))]
assert packed_rows[:21]==true_rows
assert packed_rows[21:]==false_rows
assert len(false_rows)==37
assert sum(target(m)<<r for r,m in enumerate(packed_rows))==2097151
result={'automorphisms_verified':len(autos),'prefix_orbits':len(representatives),'prefix_wirings':sum(orbit_sizes),'positive_rows':len(true_rows),'negative_rows':len(false_rows),'packed_row_order_exact_match':True,'false_row_size_counts':{k:sum(m.bit_count()==k for m in false_rows) for k in sorted(set(m.bit_count() for m in false_rows))},'orbit_sizes':orbit_sizes}
print(json.dumps(result,indent=2))
Path('/tmp/oec/pequalnp-pilot-70/sat-review/verified_symmetry.json').write_text(json.dumps({'automorphisms':autos,'representatives':representatives,'orbit_sizes':orbit_sizes}))
