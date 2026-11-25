import json
import sys
from pathlib import Path
from prune import signatures

case_path, circuit_path, output_path = map(Path, sys.argv[1:])
case = json.loads(case_path.read_text())
gates = json.loads(circuit_path.read_text())
n = case['inputs']
values = signatures(n, gates, case['tests'])
target = sum(bool(y) << i for i, (_, y) in enumerate(case['tests']))
cones = [0] * n
for k, (_, a, b) in enumerate(gates):
    cones.append(cones[a] | cones[b] | (1 << k))
best = 10**9
answer = None
for i, value in enumerate(values):
    if value == target and cones[i].bit_count() < best:
        best = cones[i].bit_count()
        answer = (i, [])
for i in range(len(values)):
    for j in range(i):
        used = cones[i] | cones[j]
        for op in [0, 1]:
            v = values[i] | values[j] if op else values[i] & values[j]
            if v == target and used.bit_count()+1 < best:
                best = used.bit_count()+1
                answer = (n+len(gates), [[op, i, j]])
            if used.bit_count()+2 >= best:
                continue
            for k in range(len(values)):
                cost = (used | cones[k]).bit_count()+2
                if cost >= best:
                    continue
                for top in [0, 1]:
                    result = v | values[k] if top else v & values[k]
                    if result == target:
                        best = cost
                        answer = (n+len(gates)+1, [[op, i, j], [top, n+len(gates), k]])
if answer is None:
    print('No exact output using at most two added gates')
    raise SystemExit(0)
output, extra = answer
all_gates = gates+extra
used = set()
def visit(i):
    if i < n or i in used:
        return
    used.add(i)
    _, a, b = all_gates[i-n]
    visit(a)
    visit(b)
visit(output)
ren = {i: i for i in range(n)}
for j, i in enumerate(sorted(used), n):
    ren[i] = j
result = [[op, ren[a], ren[b]] for i in sorted(used) for op, a, b in [all_gates[i-n]]]
assert signatures(n, result, case['tests'])[ren[output]] == target
output_path.write_text(json.dumps(result, indent=2))
print('Best exact output after <=2 new gates:',len(result),'from',len(gates),'original gates')
