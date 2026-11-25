from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / 'results/orch/lemmas/circuit_search/geometry.json'
CERTIFICATE = Path(__file__).with_name('penalty4-four-residual-geometry.json')

data = json.loads(SOURCE.read_text())
certificate = json.loads(CERTIFICATE.read_text())
edges = [tuple(edge) for edge in data['edges']]
assert len(edges) == len(set(edges)) == 52
assert all(0 <= a < 13 <= b < 26 for a, b in edges)
assert all(sum(v in edge for edge in edges) == 4 for v in range(26))
neighbors = [0] * 13
for a, b in edges:
    neighbors[a] |= 1 << (b - 13)

mixed_max = 0
large = []
for points in range(1 << 13):
    forbidden_lines = 0
    for p in range(13):
        if (points >> p) & 1:
            forbidden_lines |= neighbors[p]
    lines = ((1 << 13) - 1) ^ forbidden_lines
    size = points.bit_count() + lines.bit_count()
    if points and lines:
        mixed_max = max(mixed_max, size)
    if size >= 12:
        large.append([points, lines, size])
assert mixed_max == certificate['mixed_independent_maximum'] == 10
assert large == certificate['large_independent_closures']
assert len(large) == 15

records = []
for side in range(2):
    for missing in range(13):
        cover = (((1 << 13) - 1) ^ (1 << missing)) << (13 * side)
        deleted = [list(edge) for edge in edges
                   if not ((cover >> edge[0]) & 1 or (cover >> edge[1]) & 1)]
        assert len(deleted) == 4
        center = missing + 13 * side
        assert all(center in edge for edge in deleted)
        records.append({'cover_mask': cover, 'deleted_star_center': center,
                        'residual_edges': deleted})
assert records == certificate['independent_12sets']
print('PASS: all 8192 point-subset closures checked; mixed independent maximum 10.')
print('PASS: exactly 26 independent 12-sets; each leaves precisely one four-edge star.')
print('Scope: finite geometry only; no circuit exclusion or Lean theorem claimed.')
