from pathlib import Path
import json
import itertools

job = Path(__file__).resolve().parent
root = job.parent / 'and-count-sat'
results = {}
for name in ['signed5-4-witness.json', 'signed6-5-witness.json']:
    data = json.loads((job / name).read_text())
    words = [[(c, 1 if s else -1) for c, s in word] for word in data['words']]
    n = len(words)
    assert all(len(w) <= data['width'] and len({c for c, s in w}) == len(w) for w in words)
    feasible = set()
    for assignment in itertools.product([-1, 0, 1], repeat=data['coords']):
        feasible.add(sum(1 << i for i, word in enumerate(words)
                         if not any(assignment[c] == s for c, s in word)))
    assert all(mask in feasible for mask in range(1 << n) if mask.bit_count() <= data['separate'])
    results[name] = {'assignments': 3 ** data['coords'], 'all_required_subsets_separated': True,
                     'unrealizable_subsets': [m for m in range(1 << n) if m not in feasible]}

rows = json.loads((job / 'structural-max-independent.json').read_text())['rows']
assert len(rows) == 704 and len({tuple(x) for x in rows}) == 704
neighbors = [sum(1 << line for line in range(13) if (point - line) % 13 in {0, 1, 3, 9})
             for point in range(13)]
computed = []
for points in range(8192):
    excluded = 0
    for point in range(13):
        if points >> point & 1:
            excluded |= neighbors[point]
    lines = 8191 ^ excluded
    if all(points >> point & 1 or neighbors[point] & lines for point in range(13)):
        computed.append((points, lines))
assert set(computed) == set(map(tuple, rows))

model = json.loads((root / 'full-point-side-countermodel.json').read_text())
words = model['words']
assert len(words) == 13 and len(model['witnesses']) == len(rows)
for (points, lines), assignment in zip(rows, model['witnesses']):
    assert len(assignment) == 12 and all(x in [-1, 0, 1] for x in assignment)
    for point, word in enumerate(words):
        hit = any(assignment[c] == s for c, s in word)
        assert hit == (not bool(points >> point & 1))

supports = [sum(1 << c for c, s in word) for word in words]
assert all(len({c for c, s in word}) == len(word) for word in words)
assert all(len(word) <= 4 for word in words)
assert all((supports[p] | supports[q]).bit_count() <= 6 for p in range(13) for q in range(p))
counts = [0] * 8192
for points, lines in rows:
    counts[points] += 1
for point in range(13):
    for mask in range(8192):
        if not mask >> point & 1:
            counts[mask] += counts[mask | (1 << point)]
unions = [0] * 8192
for mask in range(1, 8192):
    bit = mask & -mask
    unions[mask] = unions[mask ^ bit] | supports[bit.bit_length() - 1]
assert all(counts[m] <= 2 ** (12 - unions[m].bit_count()) for m in range(8192))
results['full_point_countermodel'] = {
    'maximal_false_rows': 704, 'row_separation_witnesses_checked': 704,
    'point_subset_count_bounds_checked': 8192, 'width_and_union_bounds_checked': True}
assert not any(78 + 4*s <= 8*f + 4*t for s in range(14) for f in range(14-s)
               for t in range(s+1) if f + 2*t <= 2*s)
results['no_private_block_inequalities'] = {'nonnegative_integer_solution': False}
(job.parent / 'research-independent-data-verification.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
