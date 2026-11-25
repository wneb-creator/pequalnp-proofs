"""Rebuild both exact Fano seeds from metadata; verify their complete truth tables."""
import json
import sys
from pathlib import Path

metadata = json.loads(Path(sys.argv[1]).read_text())
output_dir = Path(sys.argv[2])
output_dir.mkdir(parents=True, exist_ok=True)
n = metadata['n']
edges = metadata['edges']
tests = metadata['tests']
assert n == 14 and len(edges) == 21 and len(tests) == 58

def target(mask):
    return any((mask >> a) & (mask >> b) & 1 for a, b in edges)

def verify(gates):
    for mask in range(1 << n):
        wires = [(mask >> i) & 1 for i in range(n)]
        for j, (op, a, b) in enumerate(gates):
            assert op in [0, 1] and 0 <= a < n + j and 0 <= b < n + j
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        assert bool(wires[-1]) == target(mask)

def save(name, gates):
    verify(gates)
    truth = sum(1 << j for j, mask in enumerate(tests) if target(mask))
    columns = [sum(1 << j for j, mask in enumerate(tests) if mask >> i & 1) for i in range(n)]
    text = f'{n} 26 {len(tests)} {truth} {len(gates)}\n'
    text += ' '.join(map(str, columns)) + '\n'
    text += '\n'.join(' '.join(map(str, gate)) for gate in gates) + '\n'
    (output_dir / name).write_text(text)

save('fano-sls.input', metadata['upper_gates'])
neighbors = [[] for _ in range(n)]
for a, b in edges:
    neighbors[a].append(b)
    neighbors[b].append(a)
gates = []

def add(op, a, b):
    gates.append([op, a, b])
    return n + len(gates) - 1

def unite(variables):
    active = list(variables)
    while len(active) > 1:
        active.append(add(1, active.pop(), active.pop()))
    return active[0]

center = 1
left = unite(neighbors[7])
right = unite(neighbors[center])
rectangle = add(0, left, right)
filter_wire = add(1, center, 7)
terms = [add(0, rectangle, filter_wire)]
for line in range(8, 14):
    terms.append(add(0, line, unite([point for point in neighbors[line] if point != center])))
unite(terms)
assert len(gates) == 29
save('fano-dirty29-sls.input', gates)
print(json.dumps({'inputs_verified_per_seed': 1 << n, 'gate_counts': [27, 29]}))
