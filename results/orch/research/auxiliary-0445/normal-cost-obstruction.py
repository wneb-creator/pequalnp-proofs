import json
from pathlib import Path

# Auxiliary one-output example, not a counterexample to the posted theorem.
# L={0,1,3,9}; f=b OR c OR d OR (a AND (u OR v)) OR (a AND (r OR s)).
line = {0, 1, 3, 9}
gates = [(2, 4, False), (0, 13, True), (5, 6, False), (0, 15, True),
         (14, 16, False), (1, 3, False), (18, 9, False), (17, 19, False)]
costs = [1] * 13
for a, b, is_and in gates:
    costs.append(min(costs[a], costs[b]) if is_and else min(5, costs[a] + costs[b]))
assert costs[-1] == 5
band_errors = 0
global_upper_errors = 0
global_differences = 0
for mask in range(8192):
    values = [bool(mask >> p & 1) for p in range(13)]
    for a, b, is_and in gates:
        values.append(values[a] and values[b] if is_and else values[a] or values[b])
    target = any(mask >> p & 1 for p in line)
    global_upper_errors += bool(values[-1] and not target)
    global_differences += values[-1] != target
    if mask.bit_count() in (7, 8):
        band_errors += values[-1] != target
assert band_errors == global_upper_errors == 0
assert global_differences > 0
result = {
    'scope': 'one-output obstruction to semantic four-zero certificate implying additive cost at most four; not a gap counterexample',
    'line': sorted(line), 'gates': gates, 'out': 20,
    'computed_capped_cost': costs[-1], 'band_rows': 3003,
    'band_errors': band_errors, 'global_upper_errors': global_upper_errors,
    'global_differences': global_differences,
    'note': 'Factoring the two a-conjuncts gives a seven-gate implementation of the same function with capped cost four; multi-output sharing may prevent deleting those original branches.'
}
Path('/tmp/oec/pequalnp-pilot-21/packing-review/normal-cost-obstruction.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
