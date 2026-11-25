import hashlib
import itertools
import json
from pathlib import Path


root = Path(__file__).resolve().parent
data = json.loads((root.parent / 'plane2056-sat' / 'plane2056-data.json').read_text())
original = json.loads((root / 'full-reused-dirty-seeds.json').read_text())
edges, rows = data['edges'], data['rows']
n = 26
positive = (1 << len(edges)) - 1
negative = ((1 << len(rows)) - 1) ^ positive
inputs = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
neighbors = [[] for _ in range(n)]
for p, line in edges:
    neighbors[p].append(line)
    neighbors[line].append(p)
center_examples = {tuple(seed['centers']): seed for seed in original}
assert len(center_examples) == 52
seeds = []
for (b, c), example in sorted(center_examples.items()):
    a_leaves = [point for point in neighbors[c] if point != b]
    d_leaves = [line for line in neighbors[b] if line != c]
    for a_count, d_count in [(1, 2), (2, 1), (2, 2)]:
        for a_set in itertools.combinations(a_leaves, a_count):
            for d_set in itertools.combinations(d_leaves, d_count):
                assert all(d not in neighbors[a] for a in a_set for d in d_set)
                gates = []

                def gate(op, u, v):
                    gates.append([op, u, v])
                    return n + len(gates) - 1

                def fold(values):
                    assert values
                    result = values[0]
                    for value in values[1:]:
                        result = gate(1, result, value)
                    return result

                left = fold([b] + list(a_set))
                right = fold([c] + list(d_set))
                dirty = gate(0, left, right)
                t_leaves = [line for line in d_leaves if line not in d_set]
                s_leaves = [point for point in a_leaves if point not in a_set]
                assert t_leaves and s_leaves
                b_context = gate(1, dirty, fold(t_leaves))
                c_context = gate(1, dirty, fold(s_leaves))
                b_star = gate(0, b_context, b)
                c_star = gate(0, c_context, c)
                region = gate(1, b_star, c_star)
                assert len(gates) == 10 and region == 35
                for op, u, v in example['gates'][10:]:
                    assert not (26 <= u < 35) and not (26 <= v < 35)
                    gates.append([op, u, v])
                output = example['output']
                assert len(gates) == 67
                values = inputs.copy()
                zero = inputs.copy()
                one = inputs.copy()
                violations = 0
                dominated = []
                for j, (op, u, v) in enumerate(gates):
                    assert u < len(values) and v < len(values)
                    x, y = values[u], values[v]
                    value = x | y if op else x & y
                    clean_u, clean_v = not (x & negative), not (y & negative)
                    violations += ((not op and (clean_u or clean_v))
                                   or (op and clean_u != clean_v))
                    for earlier, previous in enumerate(values):
                        if not ((value & positive) & ~previous) and not ((previous & negative) & ~value):
                            dominated.append([n + j, earlier])
                    values.append(value)
                    one.append((one[u] | one[v]) if op else (zero[u] & zero[v]))
                    zero.append((zero[u] | zero[v]) if op else 0)
                assert values[output] == positive
                assert values[dirty] & negative
                assert sum(u == dirty for _, u, _ in gates) + sum(v == dirty for _, _, v in gates) == 2
                assert violations == 0 and not dominated
                seeds.append({
                    'centers': [b, c], 'rectangle_sizes': [1 + a_count, 1 + d_count],
                    'rectangle_inputs': [[b] + list(a_set), [c] + list(d_set)],
                    'T': t_leaves, 'S': s_leaves,
                    'dirty_and_wire': dirty, 'dirty_direct_uses': 2,
                    'dirty_next_and_wires': [b_star, c_star],
                    'gates': gates, 'output': output, 'size': len(gates),
                    'normalization_violations': violations, 'dominated_gates': len(dominated),
                    'accepted_without_read1': (positive & ~one[output]).bit_count(),
                })
assert len(seeds) == 1404
destination = root / 'full-expanded-reused-dirty-seeds.json'
destination.write_text(json.dumps(seeds, separators=(',', ':')) + '\n')
print(json.dumps({
    'seeds': len(seeds), 'sizes': sorted({s['size'] for s in seeds}),
    'rectangle_classes': sorted({tuple(s['rectangle_sizes']) for s in seeds}),
    'nonread1': sorted({s['accepted_without_read1'] for s in seeds}),
    'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
}), flush=True)
