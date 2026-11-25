from pathlib import Path
from itertools import combinations
import json

scratch = Path(__file__).resolve().parent
n = 9
center = 0
leaves = [1, 2, 3]
cycle = list(range(4, 9))
edges = [(center, b) for b in leaves] + [(cycle[i], cycle[(i + 1) % 5]) for i in range(5)]
independent_pairs = [p for p in combinations(cycle, 2) if p not in edges and p[::-1] not in edges]
factors = [leaves + [v for v in cycle if v not in p] for p in independent_pairs]
gates = []
def add(op, a, b):
    gates.append([op, a, b])
    return n + len(gates) - 1
leaf_sum = add('or', add('or', 1, 2), 3)
factor_wires = []
for omitted_pair in independent_pairs:
    cover = [v for v in cycle if v not in omitted_pair]
    factor_wires.append(add('or', leaf_sum, add('or', add('or', cover[0], cover[1]), cover[2])))
value = center
chain = []
for factor in factor_wires:
    value = add('and', value, factor)
    chain.append(value - n)
terms = [value] + [add('and', a, b) for a, b in edges if center not in (a, b)]
output = terms[0]
for term in terms[1:]:
    output = add('or', output, term)
values = []
for mask in range(1 << n):
    row = [bool(mask >> i & 1) for i in range(n)]
    target = any(row[a] and row[b] for a, b in edges)
    for op, a, b in gates:
        row.append((row[a] and row[b]) if op == 'and' else (row[a] or row[b]))
    assert row[output] == target
    values.append((row, target))
ancestors = []
for op, a, b in gates:
    deps = set()
    for wire in (a, b):
        if wire >= n:
            deps.add(wire - n)
            deps.update(ancestors[wire - n])
    ancestors.append(deps)
and_gates = [j for j, gate in enumerate(gates) if gate[0] == 'and']
sound = [j for j in and_gates if all(not row[n + j] or target for row, target in values)]
assert all(i not in ancestors[j] for i in sound for j in and_gates if i != j)
dirty = [j for j in and_gates if j not in sound]
assert dirty == chain[:-1]
owned = {}
for j in and_gates:
    witnesses = []
    for a, b in edges:
        row = values[(1 << a) | (1 << b)][0]
        if row[n + j] and all(not row[n + i] for i in ancestors[j] if gates[i][0] == 'and'):
            witnesses.append([a, b])
    owned[str(j)] = witnesses
result = dict(n=n, edges=edges, gates=gates, output=output, chain_gates=chain,
              top_form_verified=True, full_table_verified=True, dirty_ands=dirty,
              owned_edges=owned, gate_count=len(gates),
              caveat='Not minimum: the five-gate chain is replaced by the three-gate clean star. This only shows TopForm itself permits cyclic dirty filters.')
(scratch / 'alg-fivefactor-topform.json').write_text(json.dumps(result, indent=2) + '\n')
print('Validated512inputs; TopForm verified; gates', len(gates), 'dirty ANDs', dirty)
