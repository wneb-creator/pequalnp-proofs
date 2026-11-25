import json
from pathlib import Path
import sys

metadata = json.loads(Path(sys.argv[1]).read_text())
log = Path(sys.argv[2])
correlated = metadata['correlated']
assert correlated and correlated['real_inputs'] == 10 and correlated['cut_inputs'] == 13
positive = {int(word) for line in log.read_text().splitlines() if line.startswith('v ')
            for word in line.split()[1:] if int(word) > 0}
assert positive, 'No satisfying assignment was printed'
cone = []
for gate in metadata['structure']:
    left = [i for i, variable in enumerate(gate['left']) if variable in positive]
    right = [i for i, variable in enumerate(gate['right']) if variable in positive]
    assert len(left) == len(right) == 1
    cone.append(['or' if gate['op'] in positive else 'and', left[0], right[0]])


def evaluate(initial, gates):
    values = list(initial)
    for op, left, right in gates:
        assert op in ('and', 'or') and 0 <= left < len(values) and 0 <= right < len(values)
        values.append(values[left] or values[right] if op == 'or' else values[left] and values[right])
    return values[-1]


for mask in range(1 << correlated['real_inputs']):
    values = [bool(mask >> i & 1) for i in range(correlated['real_inputs'])]
    values.extend(values[a] or values[b] for a, b in correlated['free_or_sums'])
    expected = any(mask >> a & 1 and mask >> b & 1 for a, b in metadata['edges'])
    assert evaluate(values, cone) == expected, ('Correlated input mismatch', mask)

full = [['or' if op else 'and', *sorted((a, b))] for op, a, b in correlated['fixed_gates']]
mapping = correlated['original_variables'] + correlated['fixed_sum_wires']
assert len(full) == 11 and len(mapping) == 13
for op, a, b in cone:
    full.append([op, *sorted((mapping[a], mapping[b]))])
    mapping.append(13 + len(full))
full.append(['or', *sorted((correlated['fixed_output'], mapping[-1]))])
assert len(full) == len(cone) + 12
edges = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
for mask in range(1 << 14):
    expected = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
    assert evaluate([bool(mask >> i & 1) for i in range(14)], full) == expected, ('Full input mismatch', mask)
log.with_suffix('.cone.json').write_text(json.dumps(cone, indent=2) + '\n')
print('VERIFIED all 1024 correlated inputs and all 16384 full inputs')
print(json.dumps(full, indent=2))
print('packed:', [a + 64 * b + (4096 if op == 'or' else 0) for op, a, b in full])
