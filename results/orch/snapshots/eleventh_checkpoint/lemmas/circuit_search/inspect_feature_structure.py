"""Inspect nesting and exact full-raw semantic necessity of every AND."""
import json
import sys
from itertools import combinations
from pathlib import Path

packet, index, candidate, report = sys.argv[1:]
case = json.loads(Path(packet).read_text())[int(index)]
data = json.loads(Path(candidate).read_text())
gates = data['gates'] if isinstance(data, dict) else data
n, raw = case['inputs'], case['raw_inputs']
assert raw <= 22
columns = [int(('1' * (1 << i) + '0' * (1 << i)) * (1 << (raw-i-1)), 2)
           for i in range(raw)]
for feature in case['features']:
    value = 0
    for i in feature['raw_indices']:
        value |= columns[i]
    columns.append(value)

def evaluate(replace=None):
    values = columns.copy()
    for i, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
        if replace and i == replace[0]:
            values.append(0 if replace[1] is None else values[replace[1]])
        else:
            values.append(values[a] | values[b] if op else values[a] & values[b])
    return values

values = evaluate()
points = (1 << len(case['group']))-1
assert all(not (values[-1] >> mask & 1)
           for mask in [points, ((1 << raw)-1)^points] + [1 << i for i in range(raw)])
depth = [0] * n
for op, a, b in gates:
    depth.append(max(depth[a], depth[b]) + int(op == 0))
redundant = [i for i, (op, a, b) in enumerate(gates) if op == 0 and
             (evaluate((i, a))[-1] == values[-1] or evaluate((i, b))[-1] == values[-1])]
false_redundant = [i for i, (op, _, _) in enumerate(gates) if op == 0 and
                   evaluate((i, None))[-1] == values[-1]]
inactive = [i for i, (op, _, _) in enumerate(gates) if op == 0 and
            not any(values[n+i] >> ((1 << p)|(1 << line)) & 1 for p, line in case['edges'])]
used = {n+len(gates)-1}
for i in range(len(gates)-1, -1, -1):
    if n+i in used:
        used.update(gates[i][1:])
edge_masks = {(1 << p)|(1 << line) for p, line in case['edges']}
small_masks = [0] + [1 << i for i in range(raw)]
small_masks += [(1 << a)|(1 << b) for a, b in combinations(range(raw), 2)
                if ((1 << a)|(1 << b)) not in edge_masks]
witness = next((dict(raw_mask=mask, and_gate=i) for mask in small_masks
                if not (values[-1] >> mask & 1)
                for i, (op, a, b) in enumerate(gates)
                if op == 0 and a != b and n+i in used and values[n+i] >> mask & 1), None)
result = dict(and_depth=depth[-1], redundant_ands=redundant,
              false_redundant_ands=false_redundant,
              positive_inactive_ands=inactive, raw_assignments=1 << raw, guards_pass=True,
              suppressed_dirty_witness=witness)
Path(report).write_text(json.dumps(result, indent=2))
print(result)
