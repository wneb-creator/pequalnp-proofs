from itertools import combinations, permutations
from pathlib import Path
import json

lines = [frozenset((l, (l+1) % 7, (l+3) % 7)) for l in range(7)]
line_lookup = {line: l for l, line in enumerate(lines)}
automorphisms = []
for perm in permutations(range(7)):
    image = [frozenset(perm[p] for p in line) for line in lines]
    if all(line in line_lookup for line in image):
        automorphisms.append(tuple(perm) + tuple(7 + line_lookup[line] for line in image))
assert len(automorphisms) == 168
duality = tuple(7 + (-p) % 7 for p in range(7)) + tuple((-l) % 7 for l in range(7))
automorphisms += [tuple(duality[perm[i]] for i in range(14))
                  for perm in automorphisms.copy()]
edges = {frozenset((p, 7+l)) for l in range(7) for p in lines[l]}
assert all({frozenset(perm[v] for v in edge) for edge in edges} == edges
           for perm in automorphisms)
unseen = {frozenset(pair) for pair in combinations(range(14), 2)}
orbits = []
for rep in [(0, 1), (0, 7), (0, 9)]:
    orbit = {frozenset((perm[rep[0]], perm[rep[1]])) for perm in automorphisms}
    assert orbit <= unseen
    unseen -= orbit
    orbits.append({'representative': rep, 'size': len(orbit),
                   'pairs': sorted(sorted(pair) for pair in orbit)})
assert not unseen
assert sorted(orbit['size'] for orbit in orbits) == [21, 28, 42]
out = {'graph_automorphisms': len(automorphisms), 'orbits': orbits}
(Path(__file__).parent / 'automorphism-orbits.json').write_text(json.dumps(out, indent=2) + '\n')
print('Verified336Fano graph automorphisms and all91 distinct input pairs.')
for orbit in orbits:
    print('representative', orbit['representative'], 'orbit size', orbit['size'])
