"""Finite orbit check for incident flags after fixing first OR inputs {0,1}."""
import itertools
import json
from pathlib import Path

data = json.loads(Path(__file__).with_name('counterexample_2583_data.json').read_text())
coords = [tuple(v) for v in data['coordinates']]
index = {v: i for i, v in enumerate(coords)}
edges = {tuple(e) for e in data['edges']}

def norm(v):
    first = next(x for x in v if x)
    return tuple(x * (1 if first == 1 else 2) % 3 for x in v)

def mul(m, v):
    return tuple(sum(m[i][j] * v[j] for j in range(3)) % 3 for i in range(3))

def inverse(m):
    a = [list(row) + [int(i == j) for j in range(3)] for i, row in enumerate(m)]
    for c in range(3):
        pivot = next((r for r in range(c, 3) if a[r][c]), None)
        if pivot is None:
            return None
        a[c], a[pivot] = a[pivot], a[c]
        scale = 1 if a[c][c] == 1 else 2
        a[c] = [x * scale % 3 for x in a[c]]
        for r in range(3):
            if r != c:
                factor = a[r][c]
                a[r] = [(x - factor * y) % 3 for x, y in zip(a[r], a[c])]
    return [row[3:] for row in a]

actions = []
for flat in itertools.product(range(3), repeat=9):
    if next((x for x in flat if x), 0) != 1:
        continue
    m = [flat[3*i:3*i+3] for i in range(3)]
    inv = inverse(m)
    if inv is None:
        continue
    point = [index[norm(mul(m, v))] for v in coords]
    if {point[0], point[1]} != {0, 1}:
        continue
    inv_t = list(zip(*inv))
    line = [index[norm(mul(inv_t, v))] for v in coords]
    assert {(point[p], 13 + line[l-13]) for p, l in edges} == edges
    actions.append((point, line))

remaining = set(edges)
orbits = []
while remaining:
    p, l = min(remaining)
    orbit = {(point[p], 13 + line[l-13]) for point, line in actions}
    assert orbit <= remaining
    remaining -= orbit
    orbits.append(sorted(orbit))
print(json.dumps({'stabilizer_size': len(actions), 'orbits': orbits}, indent=2))
