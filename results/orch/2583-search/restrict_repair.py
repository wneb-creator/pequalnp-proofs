#!/usr/bin/env python3
"""Try zero restrictions covering all erroneous pairs, then restore true stars."""
import itertools
import json
import pathlib
import sys

directory = pathlib.Path(sys.argv[1])
problem = json.loads((directory / 'plane3.json').read_text())
candidate = json.loads((directory / 'best63-mixed.json').read_text())
analysis = json.loads((directory / 'mixed-analysis.json').read_text())
assert not analysis['augmented_graph_false_positives']
extras = analysis['extra_quadratic_minterms']
vertices = sorted({v for edge in extras for v in edge})


def restrict(zeros):
    mapping = [None if i in zeros else i for i in range(26)]
    gates, known = [], {}
    for gate in candidate['gates']:
        a, b, op = mapping[gate['a']], mapping[gate['b']], gate['op']
        if a is None and b is None or op == 'and' and (a is None or b is None):
            mapping.append(None)
        elif a is None:
            mapping.append(b)
        elif b is None or a == b:
            mapping.append(a)
        else:
            key = (op, min(a, b), max(a, b))
            if key not in known:
                known[key] = 26 + len(gates)
                gates.append(dict(op=op, a=key[1], b=key[2]))
            mapping.append(known[key])
    output = mapping[candidate['output']]
    assert output is not None
    used, stack = set(), [output]
    while stack:
        wire = stack.pop()
        if wire in used:
            continue
        used.add(wire)
        if wire >= 26:
            gate = gates[wire-26]
            stack.extend([gate['a'], gate['b']])
    compact, renaming = [], dict((i, i) for i in range(26))
    for i, gate in enumerate(gates):
        if i+26 in used:
            renaming[i+26] = 26 + len(compact)
            compact.append(dict(op=gate['op'], a=renaming[gate['a']], b=renaming[gate['b']]))
    return compact, renaming[output]


results = []
for size in range(1, len(vertices)+1):
    for choice in itertools.combinations(vertices, size):
        zeros = set(choice)
        if any(a not in zeros and b not in zeros for a, b in extras):
            continue
        gates, output = restrict(zeros)
        baseline = len(gates)
        assigned = {v: [] for v in choice}
        for a, b in problem['edges']:
            if a in zeros:
                assigned[a].append(b)
            elif b in zeros:
                assigned[b].append(a)
        for center, neighbors in assigned.items():
            if not neighbors:
                continue
            wire = neighbors[0]
            for neighbor in neighbors[1:]:
                gates.append(dict(op='or', a=wire, b=neighbor))
                wire = 25 + len(gates)
            gates.append(dict(op='and', a=center, b=wire))
            wire = 25 + len(gates)
            gates.append(dict(op='or', a=output, b=wire))
            output = 25 + len(gates)
        result = dict(zeros=list(choice), restricted_gates=baseline,
                      restored_gates=len(gates))
        results.append(result)
        if len(gates) <= 63:
            out = dict(inputs=26, gates=gates, output=output, repair=result)
            (directory / 'repaired63.json').write_text(json.dumps(out, indent=2)+'\n')
            print('POTENTIAL EXACT REPAIR', result)
results.sort(key=lambda x: (x['restored_gates'], x['restricted_gates']))
(directory / 'restriction-repairs.json').write_text(json.dumps(results, indent=2)+'\n')
print('best', results[:5])
