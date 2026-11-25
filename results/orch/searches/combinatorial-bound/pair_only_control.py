from itertools import combinations
from pathlib import Path
import json


labels = list(combinations(range(1, 5), 2))
clauses = [list(range(6)), list(range(6, 12))]
for t in range(1, 5):
    clauses.append([i for i, u in enumerate(labels) if t in u] +
                   [6 + i for i, u in enumerate(labels) if t not in u])


def value(mask):
    return all(any(mask >> v & 1 for v in c) for c in clauses)


matching = {(i, i + 6) for i in range(6)}
accepted_pairs = {(a, b) for a, b in combinations(range(12), 2)
                  if value(1 << a | 1 << b)}
assert accepted_pairs == matching
assert not value((1 << 6) - 1)
assert not value(((1 << 6) - 1) << 6)
triple = [labels.index((1, 2)), labels.index((3, 4)), 6 + labels.index((1, 3))]
mask = sum(1 << v for v in triple)
assert value(mask)
assert not any(mask >> a & 1 and mask >> b & 1 for a, b in matching)
record = {'labels_a': labels, 'labels_b_offset': 6, 'clauses': clauses,
          'and_count': len(clauses) - 1,
          'accepted_pairs': sorted(accepted_pairs),
          'all_left_value': False, 'all_right_value': False,
          'accepted_independent_triple': triple,
          'conclusion': 'Pair-only impostor. Violates BelowF; not a counterexample to any full statement.'}
Path('/tmp/oec/pequalnp-pilot-71/combinatorial-bound/pair-only-control.json').write_text(
    json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
