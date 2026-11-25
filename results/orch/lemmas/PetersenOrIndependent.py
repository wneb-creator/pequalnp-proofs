import json
from pathlib import Path
from itertools import permutations, combinations

scratch = Path('/tmp/oec/pequalnp-pilot-54')
witness = json.loads((scratch / 'petersenminus2_or8_native.witness.json').read_text())
n = witness['n']
edges = {tuple(sorted(e)) for e in witness['edges']}
assert n == 8 and len(edges) == 10
assert all(len(set(e)) == 2 and all(0 <= v < n for v in e) for e in edges)

assignment = {}
for line in (scratch / 'petersenminus2_or8_native.sol').read_text().splitlines():
    if line.startswith('v '):
        for s in line.split()[1:]:
            v = int(s)
            if v:
                assert abs(v) not in assignment
                assignment[abs(v)] = v > 0
clauses = []
current = []
for line in (scratch / 'petersenminus2_or8_native.cnf').read_text().splitlines():
    if line.startswith('p '):
        _, _, variables, clause_count = line.split()
        variables, clause_count = int(variables), int(clause_count)
    elif line and not line.startswith('c'):
        for s in line.split():
            v = int(s)
            if v:
                current.append(v)
            else:
                clauses.append(current)
                current = []
assert not current
assert len(assignment) == variables == 2016
assert len(clauses) == clause_count == 8361
for clause in clauses:
    assert any(assignment[abs(v)] == (v > 0) for v in clause)

for cycle_length in (3, 4):
    assert not any(all(tuple(sorted((vs[i], vs[(i+1) % cycle_length]))) in edges
                       for i in range(cycle_length))
                   for vs in permutations(range(n), cycle_length))

for mask in range(1 << n):
    x = [bool(mask & (1 << i)) for i in range(n)]
    os = []
    def meet(items):
        vals = []
        for kind, index in items:
            assert kind in ('input', 'or')
            assert 0 <= index < (n if kind == 'input' else len(os))
            vals.append(x[index] if kind == 'input' else os[index])
        return all(vals)
    for k in range(witness['or_gates']):
        os.append(meet(witness['witness'][str((k, 0))]) or
                  meet(witness['witness'][str((k, 1))]))
    result = meet(witness['witness']['output'])
    truth = any(x[u] and x[v] for u, v in edges)
    a, b, c = x[1] or x[4], x[0] or x[3], x[3] or x[4]
    d = x[5] or (a and b and c)
    simplified = (x[6] and a) or (x[2] and c) or (x[7] and b) or (d and (x[0] or x[1]))
    assert result == truth == simplified, (mask, result, truth, simplified)

covers = [vs for size in range(n + 1) for vs in combinations(range(n), size)
          if all(u in vs or v in vs for u, v in edges)]
tau = min(map(len, covers))
assert tau == 4
print(json.dumps({'verdict': 'PASS', 'variables': variables, 'clauses': len(clauses),
                  'full_inputs': 1 << n, 'vertices': n, 'edges': len(edges),
                  'girth_at_least_5': True, 'or_gates': 8, 'simplified_and_gates': 6,
                  'vertex_cover_number': tau, 'star_upper_bound': len(edges) + tau - 1,
                  'minimum_covers': [c for c in covers if len(c) == tau]}, indent=2))
