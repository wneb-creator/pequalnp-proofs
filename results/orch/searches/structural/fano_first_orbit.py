"""Add the reviewed first-input-pair orbit normalization to an exact Fano query."""
import argparse
import hashlib
import json
from itertools import combinations_with_replacement
from pathlib import Path

from exact_graph_sat import generate
from fano_sat import CNF


p = argparse.ArgumentParser()
p.add_argument('--source', required=True)
p.add_argument('--stem', required=True)
p.add_argument('--automorphisms', required=True)
a = p.parse_args()
data = json.loads(Path(a.source + '.json').read_text())
assert data['n'] == 14
aut_path = Path(a.automorphisms)
automorphisms = json.loads(aut_path.read_text())
edges = {tuple(sorted(e)) for e in data['edges']}
assert len(automorphisms) == 336
for permutation in automorphisms:
    assert sorted(permutation) == list(range(14))
    assert {tuple(sorted((permutation[u], permutation[v]))) for u, v in edges} == edges
minima = set()
for u, v in combinations_with_replacement(range(14), 2):
    keys = [tuple(reversed(sorted((perm[u], perm[v])))) for perm in automorphisms]
    b, a0 = min(keys)
    minima.add((a0, b))
assert minima == {(0, 0), (0, 1), (0, 7), (2, 7)}
if data['pins'] is not None:
    best = None
    best_key = None
    for permutation in automorphisms:
        mapping = {i: permutation[i] for i in range(14)}
        remaining = set(range(data['k']))
        gates = []
        keys = []
        while remaining:
            ready = []
            for g in remaining:
                op, u, v = data['pins'][g]
                if u in mapping and v in mapping:
                    x, y = sorted((mapping[u], mapping[v]))
                    ready.append((y, x, op, g))
            assert ready
            y, x, op, g = min(ready)
            mapping[14 + g] = 14 + len(gates)
            gates.append((op, x, y))
            keys.append((y, x, op))
            remaining.remove(g)
        if best_key is None or keys < best_key:
            best_key, best = keys, gates
    assert tuple(best[0][1:]) in minima
    generate(14, data['edges'], data['k'], a.stem, data['and_count'], best)
    data = json.loads(Path(a.stem + '.json').read_text())
    lines = Path(a.stem + '.cnf').read_text().splitlines()
else:
    lines = Path(a.source + '.cnf').read_text().splitlines()
header = lines[0].split()
c = CNF()
c.n = int(header[2])
c.clauses = []
choices = []
for u, v in sorted(minima):
    choices.append(c.and_(data['selectors'][0][0][u], data['selectors'][0][1][v]))
c.add(*choices)
lines[0] = 'p cnf %d %d' % (c.n, int(header[3]) + len(c.clauses))
lines.extend(' '.join(map(str, clause)) + ' 0' for clause in c.clauses)
Path(a.stem + '.cnf').write_text('\n'.join(lines) + '\n')
data.update(variables=c.n, clauses=int(header[3]) + len(c.clauses),
            first_pair_representatives=sorted(minima),
            automorphism_sha256=hashlib.sha256(aut_path.read_bytes()).hexdigest())
Path(a.stem + '.json').write_text(json.dumps(data))
print(json.dumps({key: data[key] for key in
                  ['variables', 'clauses', 'first_pair_representatives']}))
