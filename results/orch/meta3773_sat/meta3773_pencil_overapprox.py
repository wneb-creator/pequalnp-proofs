from pathlib import Path
import json
import resource
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
data = json.loads((job / 'meta3773-synthesis-data.json').read_text())
core_data = json.loads((job / 'geometry-meta3773-core-data.json').read_text())
D = {0, 1, 3, 9}
point = 9
pencil = [line for line in range(13) if (point + line) % 13 in D]
restricted_union = '--union' in sys.argv
unrefined = [1, 2] if restricted_union else [2, 3]
assert all(line not in pencil for line in unrefined)

def construct(core):
    n = 24 if core else 26
    gates = []
    def gate(op, a, b):
        output = n + len(gates)
        gates.append([op, *sorted([a, b])])
        return output
    def disjoin(inputs):
        output = inputs[0]
        for value in inputs[1:]:
            output = gate(0, output, value)
        return output
    def point_wire(p):
        return p - int(core and p > point)
    def line_wire(line):
        return 12 + line - 1 if core else 13 + line
    blocks = {}
    union_signals = []
    union = {p for p in range(13) if any((p + line) % 13 in D for line in unrefined)}
    for line in pencil:
        points = [p for p in range(13) if p != point and (p + line) % 13 in D]
        selected = [p for p in points if p in union]
        others = [p for p in points if p not in union]
        ordered = selected + others if restricted_union else points
        pair = gate(0, point_wire(ordered[0]), point_wire(ordered[1]))
        blocks[line] = gate(0, pair, point_wire(ordered[2]))
        if restricted_union:
            assert len(selected) in [1, 2]
            union_signals.append(pair if len(selected) == 2 else point_wire(selected[0]))
    x = disjoin(union_signals if restricted_union else
        (list(blocks.values()) if core else [point] + list(blocks.values())))
    y = disjoin([line_wire(line) for line in unrefined])
    terms = [gate(1, x, y)]
    for line in range(1 if core else 0, 13):
        if line in unrefined:
            continue
        if line in pencil:
            neighbors = blocks[line] if core else gate(0, point, blocks[line])
        else:
            neighbors = disjoin([point_wire(p) for p in range(13)
                if (p + line) % 13 in D])
        terms.append(gate(1, line_wire(line), neighbors))
    output = disjoin(terms)
    if core:
        reserve_b = disjoin([line_wire(line) for line in pencil if line != 0])
        return gates, [output, blocks[0], reserve_b]
    return gates, [output]

whole, whole_outputs = construct(False)
assert len(whole) == (60 if restricted_union else 61) and whole[0] == [0, 0, 1]
whole_errors = []
for i, sample in enumerate(data['positive'] + data['negative_full']):
    wires = [bool(sample >> j & 1) for j in range(26)]
    for op, a, b in whole:
        wires.append(wires[a] and wires[b] if op else wires[a] or wires[b])
    if wires[whole_outputs[0]] != (i < 52):
        whole_errors.append(i)
assert all(i >= 52 for i in whole_errors)
out = {'inputs': 26, 'gates': whole, 'outputs': whole_outputs,
    'operation_convention': '0=OR,1=AND', 'point_pencil': point,
    'unrefined_lines': unrefined, 'errors': len(whole_errors), 'error_rows': whole_errors}
(job / ('meta3773-pencil60-union-overapprox.json' if restricted_union else
    'meta3773-pencil61-p9-overapprox.json')).write_text(json.dumps(out) + '\n')

core, core_outputs = construct(True)
assert len(core) == 56 and core[0] == [0, 0, 1]
core_errors = []
core_positive_errors = []
for i, sample in enumerate(core_data['rows']):
    wires = [bool(sample >> j & 1) for j in range(24)]
    for op, a, b in core:
        wires.append(wires[a] and wires[b] if op else wires[a] or wires[b])
    failed = []
    for k, output in enumerate(core_outputs):
        care = bool(core_data['care'][k][i // 64] >> (i % 64) & 1)
        truth = bool(core_data['truth'][k][i // 64] >> (i % 64) & 1)
        if care and wires[output] != truth:
            failed.append(k)
    if failed:
        core_errors.append(i)
        if i < 45:
            core_positive_errors.append(i)
assert not core_positive_errors
out = {'inputs': 24, 'gates': core, 'outputs': core_outputs,
    'operation_convention': '0=OR,1=AND', 'point_pencil': point,
    'unrefined_lines': unrefined, 'errors': len(core_errors), 'error_rows': core_errors}
(job / ('meta3773-pencil56-union-core-overapprox.json' if restricted_union else
    'meta3773-pencil56-core-overapprox.json')).write_text(json.dumps(out) + '\n')
print(json.dumps({'whole_gates': len(whole), 'whole_false_positives': len(whole_errors),
    'core_gates': len(core), 'core_failed_rows': len(core_errors),
    'core_positive_errors': len(core_positive_errors)}))
