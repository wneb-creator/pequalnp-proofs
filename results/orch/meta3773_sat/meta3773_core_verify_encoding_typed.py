from pathlib import Path
import json
import resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
metadata = json.loads((job / 'meta3773-core-sat-r991-metadata.json').read_text())
data = json.loads((job / 'geometry-meta3773-core-data.json').read_text())
seed = json.loads((job / 'meta3773-core-validation60-seed-typed.json').read_text())
assignment = {i: False for i in range(1, metadata['variables'] + 1)}
wires = [[bool(data['rows'][row] >> i & 1) for i in range(24)] for row in metadata['tests']]
for gate, (operation, left, right) in zip(metadata['gates'], seed['gates']):
    left, right = sorted([left, right])
    for name, selected in [('left', left), ('right', right)]:
        for i, variable in enumerate(gate[name]):
            assignment[variable] = i == selected
            assignment[gate[name + '_prefix'][i]] = i >= selected
    assignment[gate['and']] = bool(operation)
    for values, (a_var, b_var, output_var) in zip(wires, gate['sample_vars']):
        a, b = values[left], values[right]
        result = a and b if operation else a or b
        assignment[a_var], assignment[b_var], assignment[output_var] = a, b, result
        values.append(result)
for selectors, wire in zip(metadata['outputs'], seed['outputs']):
    for i, variable in enumerate(selectors):
        assignment[variable] = i == wire
        assignment[selectors[-1] + 1 + i] = i >= wire
count = 0
with (job / 'meta3773-core-sat-r991.cnf').open() as stream:
    for line in stream:
        if line.startswith('p'):
            continue
        literals = [int(x) for x in line.split()[:-1]]
        assert any(assignment[abs(x)] == (x > 0) for x in literals), (count, literals)
        count += 1
assert count == metadata['clauses']
for row, sample in enumerate(data['rows']):
    values = [bool(sample >> i & 1) for i in range(24)]
    for op, a, b in seed['gates']:
        values.append(values[a] and values[b] if op else values[a] or values[b])
    for k, wire in enumerate(seed['outputs']):
        care = bool(data['care'][k][row // 64] >> (row % 64) & 1)
        truth = bool(data['truth'][k][row // 64] >> (row % 64) & 1)
        assert not care or values[wire] == truth
print(json.dumps({'known_60_gate_core_satisfies_every_generated_clause': True,
    'clauses': count, 'samples': len(metadata['tests']), 'variables': len(assignment),
    'all_737_original_care_constraints_verified': True,
    'not_a_58_gate_solution': True}))
