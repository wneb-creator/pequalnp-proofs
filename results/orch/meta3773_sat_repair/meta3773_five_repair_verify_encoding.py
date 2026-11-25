from pathlib import Path
import json
import resource
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
data = json.loads((job / 'meta3773-five-patch-data.json').read_text())
round_number = int(sys.argv[1]) if len(sys.argv) > 1 else 990
stem = 'meta3773-five-repair-r' + str(round_number)
metadata = json.loads((job / (stem + '-metadata.json')).read_text())
gates = []

def gate(op, a, b):
    wire = 32 + len(gates)
    gates.append([op, *sorted([a, b])])
    return wire

stars = []
for point in range(5):
    lines = [line for p, line in data['edges'] if p == point]
    first = gate(0, lines[0], lines[1])
    second = gate(0, lines[2], lines[3])
    merged = gate(0, first, second)
    stars.append(gate(1, point, merged))
output = stars[0]
for star in stars[1:]:
    output = gate(0, output, star)
assert len(gates) == 24
old = list(gates)
remaining = set(range(24))
renaming = {i: i for i in range(32)}
gates = []
while remaining:
    ready = []
    for i in remaining:
        op, a, b = old[i]
        if a in renaming and b in renaming:
            a, b = sorted([renaming[a], renaming[b]])
            ready.append((b, a, i, op))
    b, a, i, op = min(ready)
    renaming[32 + i] = 32 + len(gates)
    gates.append([op, a, b])
    remaining.remove(i)
assert renaming[output] == 55
assignment = {i: False for i in range(1, metadata['variables'] + 1)}
for selectors in metadata['tree_choices']:
    assignment[selectors[0]] = True
    for i in range(len(selectors)):
        assignment[selectors[-1] + 1 + i] = True
wires = []
for row, (sample, desired) in enumerate(metadata['tests']):
    values = [bool(sample >> i & 1) for i in range(16)]
    for group in data['outside_groups']:
        for a, b in group['variants'][0]:
            truth = values[a] or values[b]
            expression = metadata['basis_variables'][len(values) - 16][row]
            if isinstance(expression, bool):
                assert expression == truth
            elif 'basis_auxiliary_variables' not in metadata or abs(expression) in metadata['basis_auxiliary_variables']:
                assignment[abs(expression)] = truth if expression > 0 else not truth
            else:
                assert (assignment[abs(expression)] if expression > 0 else not assignment[abs(expression)]) == truth
            values.append(truth)
    wires.append(values)
for index, (encoded, (operation, left, right)) in enumerate(zip(metadata['gates'], gates)):
    for name, chosen in [('left', left), ('right', right)]:
        for i, variable in enumerate(encoded[name]):
            assignment[variable] = i == chosen
            assignment[encoded[name + '_prefix'][i]] = i >= chosen
    assignment[encoded['and']] = bool(operation)
    if encoded.get('same_max') is not None:
        previous_operation, previous_left, previous_right = gates[index - 1]
        assignment[encoded['same_max']] = previous_right == right
        assignment[encoded['same_pair']] = previous_right == right and previous_left == left
    for values, (a_var, b_var, y_var) in zip(wires, encoded['sample_variables']):
        a, b = values[left], values[right]
        y = a and b if operation else a or b
        assignment[a_var], assignment[b_var], assignment[y_var] = a, b, y
        values.append(y)
assert all(values[-1] == expected for values, (_, expected) in zip(wires, metadata['tests']))
checked = 0
with (job / (stem + '.cnf')).open() as stream:
    for line in stream:
        if line.startswith('p'):
            continue
        literals = [int(x) for x in line.split()[:-1]]
        assert any(assignment[abs(x)] == (x > 0) for x in literals), (checked, literals)
        checked += 1
assert checked == metadata['clauses']
print(json.dumps({'known_24_gate_patch_satisfies_every_clause': True,
    'clauses': checked, 'variables': metadata['variables'], 'samples': 50}))
(job / 'meta3773-five-known24.json').write_text(json.dumps(gates) + '\n')
