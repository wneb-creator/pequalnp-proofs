import itertools, json, sys
from pathlib import Path

graph = json.loads(Path(sys.argv[1]).read_text())
n = graph['n']
edges = {tuple(sorted(e)) for e in graph['edges']}
adj = {i: {j for j in range(n) if tuple(sorted((i, j))) in edges} for i in range(n)}
A = sorted(i for i in range(n) if len(adj[i]) == 3)
C = sorted(set().union(*(adj[i] for i in A)))
B = sorted(set(range(n)) - set(A) - set(C))
gates = []
def gate(op, a, b):
    gates.append([op, a, b])
    return n + len(gates) - 1
pieces = []
for b in B:
    p, q = sorted(adj[b] & set(C))
    s = gate('or', *sorted(adj[p] & set(A)))
    t = gate('or', *sorted(adj[q] & set(A)))
    r = gate('or', p, q)
    u = gate('or', p, t)
    v = gate('or', q, s)
    w = gate('and', u, v)
    z = gate('or', b, w)
    pieces.append(gate('and', r, z))
u = gate('and', B[0], B[1])
v = gate('or', B[0], B[1])
w = gate('and', B[2], v)
pieces.append(gate('or', u, w))
output = pieces[0]
for p in pieces[1:]:
    output = gate('or', output, p)
inputs = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
target = 0
for i, j in edges:
    target |= inputs[i] & inputs[j]
def evaluate(sub=None):
    vals = inputs.copy()
    for k, (op, a, b) in enumerate(gates):
        if sub and k == sub[0]:
            vals.append(vals[sub[1]])
        else:
            vals.append(vals[a] & vals[b] if op == 'and' else vals[a] | vals[b])
    return vals[output]
assert evaluate() == target
removable = []
for k in range(len(gates)):
    for j in range(n + k):
        if evaluate((k, j)) == target:
            removable.append([k, j])
core = sorted(set(A) | set(C))
coreedges = [e for e in edges if set(e) <= set(core)]
print(json.dumps({'A': A, 'B': B, 'C': C, 'gates': len(gates),
                  'exact_truth_rows': 1 << n, 'core_edges': len(coreedges),
                  'core_degrees': [len(adj[i] & set(core)) for i in core],
                  'removable_by_single_wire_substitution': removable}, indent=2))
Path(sys.argv[2]).write_text(json.dumps({'n': n, 'edges': sorted(edges), 'gates': gates,
                                      'output': output, 'exact': True}, indent=2))
