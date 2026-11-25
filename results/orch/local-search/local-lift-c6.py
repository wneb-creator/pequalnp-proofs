from pathlib import Path
import sys
import json

lines = Path(sys.argv[1]).read_text().splitlines()
output = int(lines[1].split()[1])
component = [tuple(map(int, line.split())) for line in lines[2:]]
assert len(component) == 10
assert component[:3] == [(1, 0, 3), (1, 2, 5), (1, 1, 4)]
component_errors = []
for x in range(64):
    wires = [bool(x >> i & 1) for i in range(6)]
    for i, (op, a, b) in enumerate(component):
        assert op in (0, 1, 2) and 0 <= a < 6 + i and 0 <= b < 6 + i
        wires.append(wires[a] and wires[b] if op == 0 else
                     wires[a] or wires[b] if op == 1 else not wires[a])
    target = any(wires[i] and wires[(i + 1) % 6] for i in range(6))
    if wires[output] != target:
        component_errors.append(x)

mapping = dict(enumerate([0, 4, 3, 2, 7, 5]))
gates = []
for i, (op, a, b) in enumerate(component):
    args = [mapping[a]] if op == 2 else [mapping[a], mapping[b]]
    mapping[6 + i] = 10 + len(gates)
    gates.append(dict(op=['and', 'or', 'not'][op], inputs=args))
component_output = mapping[output]
for center, prefix in [(1, 10), (8, 11), (9, 12)]:
    p = 10 + len(gates)
    gates.append(dict(op='or', inputs=[prefix, 6]))
    gates.append(dict(op='and', inputs=[center, p]))
for left, right in [(component_output, 21), (26, 23), (27, 25)]:
    gates.append(dict(op='or', inputs=[left, right]))
assert len(gates) == 19

used = set()


def visit(wire):
    if wire < 10 or wire in used:
        return
    used.add(wire)
    for source in gates[wire - 10]['inputs']:
        visit(source)


visit(28)
inserted_not = None
if not any(g['op'] == 'not' for g in gates):
    for i in range(3, 10):
        if 10 + i not in used:
            gates[i] = dict(op='not', inputs=[0])
            inserted_not = i
            break

edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
errors = []
for x in range(1024):
    wires = [bool(x >> i & 1) for i in range(10)]
    for i, g in enumerate(gates):
        assert all(0 <= j < 10 + i for j in g['inputs'])
        args = [wires[j] for j in g['inputs']]
        wires.append(all(args) if g['op'] == 'and' else
                     any(args) if g['op'] == 'or' else not args[0])
    target = any(wires[a] and wires[b] for a, b in edges)
    if wires[28] != target:
        errors.append(x)
nots = sum(g['op'] == 'not' for g in gates)
print(json.dumps(dict(gates=gates, output=28, size=19, not_count=nots,
                     inserted_unused_not=inserted_not,
                     component_errors=component_errors, petersen_errors=errors,
                     refutes_2592=(not component_errors and not errors and nots > 0)), indent=2))
