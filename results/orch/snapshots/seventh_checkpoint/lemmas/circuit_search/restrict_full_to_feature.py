import json
import pathlib
import sys

packet, case_index, source, destination = sys.argv[1:]
case = json.loads(pathlib.Path(packet).read_text())[int(case_index)]
original = json.loads(pathlib.Path(source).read_text())
n, raw = case['inputs'], case['raw_inputs']
local = {original: i for i, original in enumerate(case['input_original'])}
aliases = {1 << i: i for i in range(raw)}
for i, feature in enumerate(case['features']):
    aliases[sum(1 << j for j in feature['raw_indices'])] = raw+i
ren, support = {}, {}
for i in range(26):
    ren[i] = local.get(i, -1)
    support[i] = 1 << local[i] if i in local and i >= 13 else None
gates = []
for i, (op, a, b) in enumerate(original):
    assert op in (0, 1) and 0 <= a < 26+i and 0 <= b < 26+i
    left, right = ren[a], ren[b]
    support[26+i] = support[a] | support[b] if op and support[a] is not None and support[b] is not None else None
    if left == right:
        value = left
    elif left == -1 or right == -1:
        value = (right if left == -1 else left) if op else -1
    elif support[26+i] in aliases:
        value = aliases[support[26+i]]
    else:
        value = n+len(gates)
        gates.append([op, left, right])
    ren[26+i] = value
output = ren[25+len(original)]
used = {output}
for i in range(len(gates)-1, -1, -1):
    if n+i in used:
        used.update(gates[i][1:])
mapping, compact = {i: i for i in range(n)}, []
for i, (op, a, b) in enumerate(gates):
    if n+i in used:
        mapping[n+i] = n+len(compact)
        compact.append([op, mapping[a], mapping[b]])
assert mapping[output] == n+len(compact)-1
degree = [0 if original < 13 else 1 for original in case['input_original']]+[1]*len(case['features'])
for op, a, b in compact:
    degree.append(max(degree[a], degree[b]) if op else degree[a]+degree[b])
pathlib.Path(destination).write_text(json.dumps(compact)+'\n')
print(dict(case=case['name'], gates=len(compact), ands=sum(op == 0 for op, _, _ in compact),
           formal_line_degree=degree[-1], within_budget=len(compact) <= case['max_gates']))
