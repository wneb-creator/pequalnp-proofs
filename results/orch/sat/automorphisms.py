import itertools
import json
from pathlib import Path

edges = {tuple(sorted(e)) for e in
         [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
          (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]}
pairs = list(itertools.combinations(range(5),2))
adj = lambda u,v: tuple(sorted((u,v))) in edges
disjoint = lambda a,b: not (set(a)&set(b))
order = [0,1,4,5,2,3,6,7,8,9]
mapping = {0:(0,1),1:(2,3)}
def search(pos):
    if pos == len(order):
        return dict(mapping)
    u = order[pos]
    if u in mapping:
        return search(pos+1)
    for pair in pairs:
        if pair in mapping.values():
            continue
        if all(adj(u,v)==disjoint(pair,old) for v,old in mapping.items()):
            mapping[u]=pair
            found=search(pos+1)
            if found:
                return found
            del mapping[u]
    return None
mapping = search(0)
assert mapping is not None
inverse = {p:v for v,p in mapping.items()}
autos=[]
for perm in itertools.permutations(range(5)):
    auto=[inverse[tuple(sorted((perm[a],perm[b])))] for a,b in [mapping[v] for v in range(10)]]
    image={tuple(sorted((auto[u],auto[v]))) for u,v in edges}
    assert image == edges
    autos.append(auto)
assert len({tuple(a) for a in autos}) == 120
orbit=[]
for u in range(10):
    row=[]
    for v in range(10):
        target=0 if u==v else 1 if adj(u,v) else 2
        index=next(i for i,a in enumerate(autos) if a[u]==0 and a[v]==target)
        row.append(index)
    orbit.append(row)
out=Path('/tmp/oec/pequalnp-pilot-110/sat_strategy/automorphisms.json')
out.write_text(json.dumps({'kneser_labels':mapping,'automorphisms':autos,'ordered_pair_orbits':orbit},indent=2)+'\n')
print('Verified 120 distinct graph automorphisms and all 100 ordered-pair orbit witnesses.')
print('Kneser labels:',mapping)
