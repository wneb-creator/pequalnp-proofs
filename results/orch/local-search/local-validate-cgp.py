from pathlib import Path
import json
import sys

source = Path(sys.argv[1])
lines = source.read_text().splitlines()
out = int(lines[1].split()[1])
gates = [tuple(map(int, line.split())) for line in lines[2:]]
used = set()


def visit(wire):
    if wire < 10 or wire in used:
        return
    assert 10 <= wire < 10 + len(gates)
    used.add(wire)
    op, a, b = gates[wire - 10]
    assert op in (0, 1, 2)
    assert 0 <= a < wire and 0 <= b < wire
    visit(a)
    if op != 2:
        visit(b)


visit(out)
mapping = {i: i for i in range(10)}
compact = []
for wire in sorted(used):
    op, a, b = gates[wire - 10]
    inputs = [mapping[a]] if op == 2 else [mapping[a], mapping[b]]
    mapping[wire] = 10 + len(compact)
    compact.append(dict(op=['and', 'or', 'not'][op], inputs=inputs))
compact_out = mapping[out]
nots = sum(g['op'] == 'not' for g in compact)
padded = False
if nots == 0 and len(compact) <= 18:
    compact.append(dict(op='not', inputs=[0]))
    nots = 1
    padded = True

edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
         (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
         (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
errors = []
for x in range(1024):
    wires = [bool(x >> i & 1) for i in range(10)]
    for g in compact:
        args = [wires[i] for i in g['inputs']]
        wires.append(all(args) if g['op'] == 'and' else
                     any(args) if g['op'] == 'or' else not args[0])
    actual = wires[compact_out]
    expected = any(wires[a] and wires[b] for a, b in edges)
    if actual != expected:
        errors.append(x)

result = dict(gates=compact, output=compact_out, size=len(compact),
              not_count=nots, padded_unused_not=padded,
              truth_table_errors=errors,
              refutes_2592=(not errors and len(compact) <= 19 and nots > 0))
print(json.dumps(result, indent=2))
