from pathlib import Path
from itertools import combinations
import json

scratch = Path(__file__).resolve().parent
center = 0
leaves = [1, 2, 3]
cycle = list(range(4, 9))
edges = [(center, b) for b in leaves] + [(cycle[i], cycle[(i + 1) % 5]) for i in range(5)]
independent_pairs = [p for p in combinations(cycle, 2) if p not in edges and p[::-1] not in edges]
factors = [leaves + [v for v in cycle if v not in p] for p in independent_pairs]
for mask in range(512):
    x = [bool(mask >> i & 1) for i in range(9)]
    target = any(x[a] and x[b] for a, b in edges)
    output = x[center] and all(any(x[v] for v in factor) for factor in factors)
    assert not output or target
witnesses = []
for omitted in range(5):
    witness = [center] + list(independent_pairs[omitted])
    x = [i in witness for i in range(9)]
    assert not any(x[a] and x[b] for a, b in edges)
    assert x[center] and all(any(x[v] for v in factor) for k, factor in enumerate(factors) if k != omitted)
    witnesses.append(dict(omitted_factor=omitted, independent_witness=witness))
result = dict(n=9, edges=edges, center=center, leaves=leaves, factors=factors,
              sound_full_table_checked=True, no_individually_clean_factor=True,
              every_proper_subproduct_unsound=witnesses,
              caveat='No minimum-circuit or gap-refutation claim; this only refutes an unrestricted clean-factor extraction lemma.')
(scratch / 'alg-fivefactor-star.json').write_text(json.dumps(result, indent=2) + '\n')
print('Validated512 inputs; each of5 factor omissions has explicit independent false-positive witness.')
