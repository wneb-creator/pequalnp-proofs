import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('stem')
ap.add_argument('--metadata')
ap.add_argument('--allow-positive-control', action='store_true')
args = ap.parse_args()
stem = Path(args.stem)
data = json.loads(Path(args.metadata or str(stem)+'.json').read_text())
solution = stem.with_suffix('.solution').read_text()
assert 's SATISFIABLE' in solution
values = {abs(int(v)): int(v)>0 for line in solution.splitlines()
          if line.startswith('v ') for v in line.split()[1:] if int(v)}
with stem.with_suffix('.cnf').open() as src:
    header = src.readline().split()
    assert header[:2] == ['p', 'cnf']
    count = 0
    for line in src:
        if not line.strip() or line.startswith('c'):
            continue
        clause = list(map(int, line.split()))
        assert clause[-1] == 0
        assert any(values[abs(v)] == (v > 0) for v in clause[:-1])
        count += 1
    assert count == int(header[3])
n, p, l = data['n'], data['p'], data['l']
assert n == p+l and n <= 16
gates = []
for i, (aa, bb, o) in enumerate(zip(data['A'], data['B'], data['O'])):
    a = [j for j, v in enumerate(aa) if values[v]]
    b = [j for j, v in enumerate(bb) if values[v]]
    assert len(a) == len(b) == 1 and 0 <= a[0] < b[0] < n+i
    gates.append((a[0], b[0], int(values[o])))
# One byte per assignment avoids packing logic while keeping full truth tables fast.
inputs = [int.from_bytes(bytes((x >> i) & 1 for x in range(1 << n)), 'little')
          for i in range(n)]
wires = list(inputs)
for a, b, o in gates:
    wires.append(wires[a] | wires[b] if o else wires[a] & wires[b])
edges = [tuple(e) for e in data['edges']]
assert len(set(edges)) == len(edges)
rows = [{v-p for u, v in edges if u == i} for i in range(p)]
assert all(0 <= u < p <= v < n for u, v in edges)
assert all(len(rows[i] & rows[j]) <= 1 for i in range(p) for j in range(i))
target = 0
for a, b in edges:
    target |= inputs[a] & inputs[b]
assert wires[-1] == target
live = set()
def visit(w):
    if w < n or w in live:
        return
    live.add(w)
    a, b, _ = gates[w-n]
    visit(a)
    visit(b)
visit(n+len(gates)-1)
index = {i: i for i in range(n)}
pruned = []
for i, (a, b, o) in enumerate(gates):
    if n+i in live:
        index[n+i] = n+len(pruned)
        pruned.append((index[a], index[b], o))
match = [-1]*l
def augment(v, seen):
    for u in rows[v]:
        if u in seen:
            continue
        seen.add(u)
        if match[u] < 0 or augment(match[u], seen):
            match[u] = v
            return True
    return False
tau = sum(augment(v, set()) for v in range(p))
matching_edges = [(v, p+u) for u, v in enumerate(match) if v >= 0]
assert len(matching_edges) == tau
assert len({v for v, _ in matching_edges}) == tau
assert all(e in edges for e in matching_edges)
bound = len(edges)+tau-1
missing = []
for a, b in edges:
    poly = [{(1, 0)} if i == a else {(0, 1)} if i == b else set() for i in range(n)]
    for u, v, o in pruned:
        poly.append(poly[u] | poly[v] if o else
                    {(min(2, x+z), min(2, y+t)) for x, y in poly[u] for z, t in poly[v]})
    if (1, 1) not in poly[-1]:
        missing.append((a, b))
if not args.allow_positive_control:
    assert len(pruned) < bound and missing
result = dict(n=n, p=p, l=l, edges=edges, gates=pruned,
              original_size=len(gates), live_size=len(pruned), matching=tau,
              matching_edges=matching_edges,
              read1_bound=bound, saving=bound-len(pruned), missing_squarefree_edges=missing,
              full_assignment_count=1 << n, full_truth_table_verified=True,
              cnf_model_verified=True)
out = stem.with_suffix('.verified.json')
out.write_text(json.dumps(result, indent=2)+'\n')
print('Verified', len(pruned), 'live gates;', 1 << n, 'assignments;',
      'saving', bound-len(pruned), '; output', out)
