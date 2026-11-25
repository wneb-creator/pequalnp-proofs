"""Enumerate C4-free 4-by-4 cases; row sorting removes one permutation factor."""
import itertools
import json
from pathlib import Path
import serve_sat

root = Path(__file__).resolve().parent
perms = list(itertools.permutations(range(4)))
column_maps = [[sum(1 << perm[b] for b in range(4) if row >> b & 1) for row in range(16)]
               for perm in perms]

def one_side(rows):
    return min(sum(row << (4 * i) for i, row in enumerate(sorted((table[r] for r in rows), reverse=True)))
               for table in column_maps)

def canonical(rows):
    transpose = [sum(1 << a for a in range(4) if rows[a] >> b & 1) for b in range(4)]
    return min(one_side(rows), one_side(transpose))

classes = {}
for mask in range(1, 1 << 16):
    rows = [(mask >> (4 * a)) & 15 for a in range(4)]
    if any((rows[a] & rows[b]).bit_count() >= 2 for a, b in itertools.combinations(range(4), 2)):
        continue
    column_degrees = [sum(row >> b & 1 for row in rows) for b in range(4)]
    if any(row.bit_count() == 1 and column_degrees[row.bit_length() - 1] == 1 for row in rows):
        continue
    key = canonical(rows)
    classes[key] = classes.get(key, 0) + 1

folder = root / 'cases4'
folder.mkdir(exist_ok=True)
cases = []
cycle = []
for mask in sorted(classes):
    edges = [(a, b) for a in range(4) for b in range(4) if mask >> (4 * a + b) & 1]
    # Independent brute-force check of every representative's canonical label.
    brute = min(min(sum(1 << (4 * left[a] + right[b]) for a, b in edges),
                    sum(1 << (4 * left[b] + right[a]) for a, b in edges))
                for left in perms for right in perms)
    assert brute == mask
    tau = serve_sat.cover_number(4, 4, edges)
    data = {'p': 4, 'l': 4, 'edges': edges, 'mask': mask, 'cover_number': tau,
            'counterexample_gates': len(edges) + tau - 2, 'labeled_cases': classes[mask]}
    (folder / f'graph_{mask}.json').write_text(json.dumps(data, indent=2) + '\n')
    cases.append(data)
    if all(sum(a == v for a, b in edges) == 2 and sum(b == v for a, b in edges) == 2 for v in range(4)):
        cycle.append(data)
assert len(cycle) == 1
(root / 'cycle8.json').write_text(json.dumps(cycle[0], indent=2) + '\n')
report = {'classes': cases, 'class_count': len(cases), 'labeled_count': sum(classes.values()),
          'cycle8_mask': cycle[0]['mask'],
          'validation': 'Every canonical representative was cross-checked against all 1152 side permutations/swaps.'}
(root / 'case_manifest_4x4.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'class_count': len(cases), 'labeled_count': sum(classes.values()),
                  'gate_counts': sorted(set(case['counterexample_gates'] for case in cases)),
                  'cycle8_mask': cycle[0]['mask']}))
