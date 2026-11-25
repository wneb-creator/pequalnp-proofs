from pathlib import Path
import json
from itertools import combinations

base = Path(__file__).resolve().parent
values = list(map(int, (base / 'singleton-packing-input.txt').read_text().split()))
row_count, edge_count = values[:2]
assert (row_count, edge_count) == (468, 52)
rows = values[2:2 + row_count]
edges = values[2 + row_count:]
assert len(rows) == len(set(rows)) == row_count
assert len(edges) == len(set(edges)) == edge_count
assert all(row.bit_count() == 7 and row < (1 << 26) for row in rows)
assert all(edge.bit_count() == 2 and edge < (1 << 26) for edge in edges)
assert all((edge & 8191).bit_count() == (edge >> 13).bit_count() == 1 for edge in edges)
output = (base / 'singleton-packing-unpruned.log').read_text().splitlines()
blocks = list(map(int, next(line for line in output if line.startswith('BEST_BLOCK_MASKS')).split()[1:]))
assert all(1 <= block.bit_count() <= 2 and block < (1 << 26) for block in blocks)
selected = 0
for block in blocks:
    assert selected & block == 0
    selected |= block
activity = [sum(bool(row & block) for block in blocks) for row in rows]
assert max(activity) <= 2
removed = sum(bool(selected & edge) for edge in edges)
assert removed == 21
stars = []
for vertex in range(26):
    star = 1 << vertex
    for edge in edges:
        if edge & (1 << vertex):
            star |= edge
    stars.append(star)
assert len(set(stars)) == 26 and all(star.bit_count() == 5 for star in stars)
assert all((row & star).bit_count() <= 2 for row in rows for star in stars)

line_points = [set() for _ in range(13)]
for edge in edges:
    point = next(v for v in range(13) if edge >> v & 1)
    line = next(v for v in range(13) if edge >> (13 + v) & 1)
    line_points[line].add(point)
theta_families = set()
for line, points in enumerate(line_points):
    for pole in range(13):
        if pole in points:
            continue
        for triple in combinations(sorted(points), 3):
            joining = []
            for point in triple:
                choices = [j for j, incidence in enumerate(line_points) if point in incidence and pole in incidence]
                assert len(choices) == 1
                joining.append(choices[0])
            for direction in (1, 2):
                family = tuple(sorted((1 << triple[i]) | (1 << (13 + joining[(i + direction) % 3])) for i in range(3)))
                theta_families.add(family)
assert len(theta_families) == 936
for family in theta_families:
    union = 0
    for block in family:
        assert union & block == 0
        union |= block
    assert all(sum(bool(row & block) for block in family) <= 2 for row in rows)
    assert sum(bool(union & edge) for edge in edges) == 21
print(json.dumps({
    'verified': True,
    'blocks': [[v for v in range(26) if block >> v & 1] for block in blocks],
    'removed_edges': removed,
    'surviving_edges': edge_count - removed,
    'row_activity_histogram': {str(k): activity.count(k) for k in range(3)},
    'all_26_singleton_stars_verified': True,
    'all_936_theta_three_maximizers_verified': True,
    'optimality_status': 'C++ exhaustive search; not a Lean proof',
}, indent=2))
