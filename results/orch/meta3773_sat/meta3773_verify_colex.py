from pathlib import Path
import json
import resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
metadata = json.loads((job / 'meta3773-whole-1-r992-metadata.json').read_text())
circuit = []
stars = []
for line in range(13):
    points = [p for p in range(13) if (p + line) % 13 in [0, 1, 3, 9]]
    first = 26 + len(circuit)
    circuit.append(('or', points[0], points[1]))
    second = 26 + len(circuit)
    circuit.append(('or', points[2], points[3]))
    third = 26 + len(circuit)
    circuit.append(('or', first, second))
    stars.append(26 + len(circuit))
    circuit.append(('and', 13 + line, third))
output = stars[0]
for star in stars[1:]:
    circuit.append(('or', min(output, star), max(output, star)))
    output = 25 + len(circuit)
assert len(circuit) == 64
circuit = json.loads((job / 'meta3773-known64-colex.json').read_text())
assignment = {}
wires = [[bool(sample >> i & 1) for i in range(26)] for sample, desired in metadata['tests']]
for gate, (operation, left, right) in zip(metadata['gates'], circuit):
    assert left < right
    for name, selected in [('left', left), ('right', right)]:
        choices = gate[name]
        for index, variable in enumerate(choices):
            assignment[variable] = index == selected
            assignment[choices[-1] + 1 + index] = index >= selected
    assignment[gate['and']] = operation == 'and'
    for index, values in enumerate(wires):
        a, b = values[left], values[right]
        result = a and b if operation == 'and' else a or b
        base = gate['and'] + 1 + 3 * index
        assignment[base] = a
        assignment[base + 1] = b
        assignment[base + 2] = result
        values.append(result)
assert len(assignment) == metadata['variables']
assert all(values[-1] == desired for values, (sample, desired) in zip(wires, metadata['tests']))
count = 0
with (job / 'meta3773-whole-1-r992.cnf').open() as stream:
    for line in stream:
        if line.startswith('p'):
            continue
        literals = [int(x) for x in line.split()[:-1]]
        assert any(assignment[abs(x)] == (x > 0) for x in literals), (count, literals)
        count += 1
assert count == metadata['clauses']
print(json.dumps({'known_64_gate_circuit_satisfies_every_generated_clause': True,
    'clauses': count, 'samples': len(metadata['tests']), 'variables': len(assignment)}))

