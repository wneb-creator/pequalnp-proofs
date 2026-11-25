import itertools
import json
from pathlib import Path

data = json.loads(Path('matching-two-example.json').read_text())
n = data['n']
edges = data['edges']
neighbors = [set() for _ in range(n)]
for a, b in edges:
    neighbors[a].add(b)
    neighbors[b].add(a)
assert all(not (neighbors[a] & neighbors[b]) for a, b in edges)
assert all(len(neighbors[a] & neighbors[b]) <= 1
           for a, b in itertools.combinations(range(n), 2))
minimum_cover = min(mask.bit_count() for mask in range(1 << n)
                    if all(mask >> a & 1 or mask >> b & 1 for a, b in edges))
assert minimum_cover == 4
results = {}
for kind in ('safe', 'unsafe'):
    gates = data[kind + '_circuit_gates']
    output = data[kind + '_circuit_output']
    errors = []
    unsafe = []
    for assignment in range(1 << n):
        values = [bool(assignment >> i & 1) for i in range(n)]
        target = any(values[a] and values[b] for a, b in edges)
        for index, (op, a, b) in enumerate(gates):
            assert a < len(values) and b < len(values)
            value = values[a] and values[b] if op == 'and' else values[a] or values[b]
            values.append(value)
            if op == 'and' and value and not target:
                unsafe.append((index, assignment))
        if values[output] != target:
            errors.append(assignment)
    assert not errors
    if kind == 'safe':
        assert not unsafe and len(gates) == 13
    else:
        assert unsafe and len(gates) == 14
    results[kind] = {'gate_count': len(gates), 'errors': errors,
                     'unsafe_and_gate_indices': sorted({i for i, _ in unsafe}),
                     'unsafe_assignment_count': len(unsafe)}
print(json.dumps({'minimum_vertex_cover': minimum_cover, 'circuits': results}, indent=2))
