"""Build all point-subset false closures and edge rows for a compact core."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('core', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
data = json.loads(args.core.read_text())
n, k = data['input_count'], data['point_count']
edges = [tuple(e) for e in data['edges']]
assert all(0 <= a < k <= b < n for a, b in edges)
assert all(sum(a == p for a, _ in edges) == 4 for p in range(k))
rows = {(1 << a) | (1 << b): 1 for a, b in edges}
for points in range(1 << k):
    mask = points
    for line in range(k, n):
        if not any(b == line and (points >> a & 1) for a, b in edges):
            mask |= 1 << line
    assert mask not in rows
    rows[mask] = 0
assert len(rows) == len(edges) + (1 << k)
with args.output.open('w') as out:
    out.write(f'{n} {k} {len(edges)} {len(rows)}\n')
    for a, b in edges:
        out.write(f'{a} {b}\n')
    for mask, value in sorted(rows.items()):
        out.write(f'{mask} {value}\n')
print(f'n={n} points={k} edges={len(edges)} rows={len(rows)} target={data["target_gate_count"]}')
