import json
import re
import sys
from pathlib import Path

q = int(sys.argv[1])
directory = Path(sys.argv[2])
directory.mkdir(parents=True, exist_ok=True)
N = q * q + q + 1
differences = {2: {0, 1, 3}, 3: {0, 1, 3, 9}}[q]
edges = [(p, N + l) for p in range(N) for l in range(N) if (p - l) % N in differences]
assert len(edges) == N * (q + 1)
assert all(sum((p - l) % N in differences for p in range(N)) == q + 1 for l in range(N))
assert all(sum((p - l) % N in differences and (p2 - l) % N in differences for l in range(N)) == 1
           for p in range(N) for p2 in range(p))
point_neighbors = [sum(1 << (l - N) for p2, l in edges if p2 == p) for p in range(N)]
line_neighbors = [sum(1 << p for p, l2 in edges if l2 == N + l) for l in range(N)]
point_union = [0] * (1 << N)
line_union = [0] * (1 << N)
for mask in range(1, 1 << N):
    bit = mask & -mask
    i = bit.bit_length() - 1
    point_union[mask] = point_union[mask ^ bit] | point_neighbors[i]
    line_union[mask] = line_union[mask ^ bit] | line_neighbors[i]
all_side = (1 << N) - 1
false_rows = set()
for points in range(1 << N):
    lines = all_side ^ point_union[points]
    closed_points = all_side ^ line_union[lines]
    row = closed_points | (lines << N)
    assert all(not (row >> p & 1 and row >> l & 1) for p, l in edges)
    assert all(any(((row | (1 << i)) >> p & 1) and ((row | (1 << i)) >> l & 1) for p, l in edges)
               for i in range(2 * N) if not (row >> i & 1))
    false_rows.add(row)
true_rows = sorted((1 << p) | (1 << l) for p, l in edges)
tests = [(x, 1) for x in true_rows] + [(x, 0) for x in sorted(false_rows)]
budget = len(edges) + N - 2
data = {'q': q, 'N': N, 'difference_set': sorted(differences), 'edges': edges,
        'true_rows': true_rows, 'maximal_false_rows': sorted(false_rows), 'search_budget': budget}
(directory / f'plane{q}.json').write_text(json.dumps(data, indent=2) + '\n')
with (directory / f'plane{q}.txt').open('w') as f:
    f.write(f'{2 * N} {budget} {len(tests)} {len(edges)}\n')
    for mask, value in tests:
        f.write(f'{mask} {value}\n')
    for p, l in edges:
        f.write(f'{p} {l}\n')
if q == 3 and len(sys.argv) > 3:
    source = Path(sys.argv[3]).read_text()
    matches = re.findall(r'GateOp\.(and|or), \[(\d+), (\d+)\]', source)
    gates = [({'and': 0, 'or': 1}[op], int(a), int(b)) for op, a, b in matches]
    assert len(gates) == 64
    def renumber(w):
        return N + (-(w - N)) % N if N <= w < 2 * N else w
    gates = [(op, renumber(a), renumber(b)) for op, a, b in gates]
    for row, value in tests:
        wires = [bool(row >> i & 1) for i in range(2 * N)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == 0 else wires[a] or wires[b])
        assert wires[-1] == bool(value)
    (directory / 'checked64-seed.txt').write_text('\n'.join(' '.join(map(str, g)) for g in gates) + '\n')
print(f'q={q}, variables={2*N}, search_budget={budget}, incident_pairs={len(true_rows)}, maximal_false_rows={len(false_rows)}, complete_critical_rows={len(tests)}')
