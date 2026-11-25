"""Independent finite-set, metadata, and embedding audit; no search is run."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import importlib
import json
import random
import re
import sys

D = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(D))


def boundary(rows, right):
    """All maximal independent assignments, using the opposite orientation."""
    rowmasks = [sum(1 << j for j in row) for row in rows]
    closed = set()
    for b in range(1 << right):
        a = sum(1 << i for i, mask in enumerate(rowmasks) if not mask & b)
        bb = sum(1 << j for j in range(right)
                 if not any(a >> i & 1 and j in row for i, row in enumerate(rows)))
        closed.add(a | (bb << len(rows)))
    for mask in closed:
        a, b = mask & ((1 << len(rows)) - 1), mask >> len(rows)
        assert all(not (a >> i & 1 and b >> j & 1)
                   for i, row in enumerate(rows) for j in row)
        assert all((a >> i & 1) or any(b >> j & 1 for j in row)
                   for i, row in enumerate(rows))
        assert all((b >> j & 1) or any(a >> i & 1 and j in row
                   for i, row in enumerate(rows)) for j in range(right))
    return closed


def read1_missing(gates, rows, right):
    """Propagate squarefree proof-tree leaf sets of degree at most two."""
    n = len(rows) + right
    terms = [{1 << i} for i in range(n)]
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= min(a, b) <= max(a, b) < len(terms)
        terms.append({x | y for x in terms[a] for y in terms[b]
                      if not x & y and (x | y).bit_count() <= 2}
                     if op else terms[a] | terms[b])
    return sorted([i, len(rows) + j] for i, row in enumerate(rows) for j in row
                  if (1 << i) | (1 << (len(rows) + j)) not in terms[-1])


def scalar(gates, n, mask):
    values = [bool(mask >> i & 1) for i in range(n)]
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= min(a, b) <= max(a, b) < len(values)
        values.append(values[a] and values[b] if op else values[a] or values[b])
    return values[-1]


def check_saved(module, name, rows, right):
    saved = json.loads((D / name).read_text())
    gates = saved['circuit']
    assert len(gates) == saved.get('gates', saved.get('gate_count'))
    missing = read1_missing(gates, rows, right)
    recorded = saved.get('nonread', saved.get('non_read1_pairs'))
    if recorded is not None:
        assert missing == sorted(recorded), (name, missing, recorded)
    if module is not None:
        assert module.bad_read1(gates) == [tuple(pair) for pair in
               sorted(missing, key=lambda p: (p[1], p[0]))]
    print('control metadata PASS', name, 'gates', len(gates), 'nonread', missing)
    return gates


summary = json.loads((D / 'summary.json').read_text())
for run in summary['runs']:
    last = (D / run['log']).read_text().splitlines()[-1]
    assert last.startswith('finished ')
    if run['log'] == 'run.log':
        actual = json.loads(last.removeprefix('finished '))
        counts = actual['queries'], actual['seeds'], actual['best']
    else:
        match = re.match(r'finished (\d+) (\d+) (\d+) (\d+) ', last)
        assert match
        cuts, starts, best, nonread = map(int, match.groups())
        assert nonread == run['best_nonread']
        counts = cuts, starts, best
    assert counts == (run['cuts'], run['starts'], run['best'])
assert sum(r['cuts'] for r in summary['runs']) == summary['total_cuts'] == 131399
assert sum(r['starts'] for r in summary['runs']) == summary['total_starts'] == 2259
print('finished-log totals PASS', summary['total_cuts'], summary['total_starts'])

q3rows = [{l for l in range(13) if (p - l) % 13 in (0, 1, 3, 9)}
          for p in range(13)]
q3boundary = boundary(q3rows, 13)
one = importlib.import_module('exact_rewrite')
plane = importlib.import_module('counterexample_q3_repair')
assert len(q3boundary) == 704 and q3boundary == set(plane.NEGATIVE)
assert len(plane.POSITIVE) == len(set(plane.POSITIVE)) == 52
assert set(plane.POSITIVE) == {(1 << p) | (1 << (13 + l))
                             for p, row in enumerate(q3rows) for l in row}
for name in ['direct65-control.json', 'best-76131.json']:
    check_saved(None, name, q3rows, 13)
seed65 = importlib.import_module('seed65')
assert seed65.c == [tuple(g) for g in
                   json.loads((D / 'direct65-control.json').read_text())['circuit']]
print('q3 boundary and 65-gate seed replay PASS', 52, 704)

grid = importlib.import_module('two_pencil')
gridrows = [{i, j + 4} for i in range(4) for j in range(4)] + [set(range(4)), set(range(4, 8))]
assert gridrows == [set(row) for row in grid.P]
assert boundary(gridrows, 8) == set(grid.neg) and len(grid.neg) == 228
assert len(grid.pos) == len(set(grid.pos)) == 40
omitted_grid = [255 ^ (mask >> 18) for mask in grid.neg]
assert sum(bool(s & 15) and bool(s & 240) for s in omitted_grid) == 225
assert set(s for s in omitted_grid if not (s & 15 and s & 240)) == {0, 15, 240}
delta = {0, 1, 4, 14, 16}
q4lines = [{(l + d) % 21 for d in delta} for l in range(21)]
assert all(len(a & b) == 1 for a, b in combinations(q4lines, 2))
assert all(sum(p in line and p2 in line for line in q4lines) == 1
           for p, p2 in combinations(range(21), 2))
assert all(sum(p in line for line in q4lines) == 5 for p in range(21))
for name in ['two-pencil-best-48.json', 'two-pencil-best-49.json']:
    gates = check_saved(grid, name, gridrows, 8)
    embedded = grid.full_plane(gates)
    selected = embedded['eight_lines']
    mapping = {i: next(iter(q4lines[selected[i // 4]] & q4lines[selected[4 + i % 4]]))
               for i in range(16)}
    mapping.update({16: 0, 17: 1})
    assert len(set(mapping.values())) == 18
    mapping.update({18 + i: 21 + l for i, l in enumerate(selected)})
    assert all({mapping[i] for i, row in enumerate(gridrows) if j in row} == q4lines[l]
               for j, l in enumerate(selected))
    expected = []
    for k, (op, a, b) in enumerate(gates, 26):
        expected.append((op, mapping[a], mapping[b])); mapping[k] = 42 + len(expected) - 1
    out = 42 + len(expected) - 1
    remaining = [l for l in range(21) if l not in selected]
    assert len(remaining) == 13 and sum(len(q4lines[l]) for l in remaining) == 65
    for l in remaining:
        points = sorted(q4lines[l]); star = points[0]
        for p in points[1:]:
            expected.append((0, star, p)); star = 42 + len(expected) - 1
        expected.append((1, star, 21 + l)); star = 42 + len(expected) - 1
        expected.append((0, out, star)); out = 42 + len(expected) - 1
    assert expected == embedded['circuit'] and len(expected) == len(gates) + 78
canonical_grid = grid.seed(random.Random(76134), 0)
assert len(canonical_grid) == 47 and grid.full_plane(canonical_grid)['gates'] == 125
print('q4 two-pencil boundary and embedding PASS', 40, 228, '+78', 'canonical 47 -> 125')

affine = importlib.import_module('affine')
off = [p for p in range(13) if 0 not in q3rows[p]]
affinerows = [{i for i, p in enumerate(off) if l in q3rows[p]} for l in range(1, 13)]
assert affinerows == [set(row) for row in affine.P]
assert boundary(affinerows, 9) == set(affine.neg) and len(affine.neg) == 197
assert len(affine.pos) == len(set(affine.pos)) == 36
omitted_affine = [511 ^ (mask >> 12) for mask in affine.neg]
assert Counter(s.bit_count() for s in omitted_affine) == {0: 1, 3: 12, 5: 54, 6: 84, 7: 36, 8: 9, 9: 1}
assert set(omitted_affine) == {sum(1 << p for p in set().union(*(affinerows[i] for i in range(12) if selected >> i & 1)))
                              for selected in range(1 << 12)}
for name in ['affine-best-45.json', 'affine-best-eligible.json']:
    gates = check_saved(affine, name, affinerows, 9)
    embedded = affine.full_plane(gates)
    assert len(embedded['circuit']) == len(gates) + 20
    assert all(scalar(embedded['circuit'], 26, mask) for mask in plane.POSITIVE)
    assert not any(scalar(embedded['circuit'], 26, mask) for mask in q3boundary)
    saved = json.loads((D / name).read_text())
    assert affine.number_present(gates, affine.point_base) == saved['point_present']
    assert affine.number_present(gates, affine.line_base) == saved['line_present']
    if name.endswith('eligible.json'):
        assert affine.pressure(gates) == 0 and len(gates) == 46
canonical_affine = affine.seed(random.Random(76135), 0)
assert len(canonical_affine) == 44 and affine.full_plane(canonical_affine)['gates'] == 64
print('q3 affine boundary and embedding PASS', 36, 197, '+20', 'canonical 44 -> 64')
print('DATASET AUDIT PASS; sampled search outcomes are not lower bounds')
