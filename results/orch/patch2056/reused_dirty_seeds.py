import hashlib
import json
from pathlib import Path


root = Path(__file__).resolve().parent
for name in ['six', 'collinear6', 'eight', 'full']:
    if name == 'full':
        data = json.loads((root.parent / 'plane2056-sat' / 'plane2056-data.json').read_text())
        k = 13
        n = 26
    else:
        data = json.loads((root / (name + '-data.json')).read_text())
        k = len(data['points'])
        n = k + len(data['lines'])
    edges = data['edges']
    rows = data['rows']
    edge_count = len(edges)
    assert all(any((r >> a & 1) and (r >> b & 1) for a, b in edges)
               == (j < edge_count) for j, r in enumerate(rows))
    positive = (1 << edge_count) - 1
    negative = ((1 << len(rows)) - 1) ^ positive
    inputs = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
    neighbors = [[] for _ in range(n)]
    for p, line in edges:
        neighbors[p].append(line)
        neighbors[line].append(p)
    seeds = []
    for c in range(k, n):
        if len(neighbors[c]) < 2:
            continue
        for b in neighbors[c]:
            for a in neighbors[c]:
                if a == b:
                    continue
                for d in neighbors[b]:
                    if d == c:
                        continue
                    assert d not in neighbors[a]
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

                    left = gate(1, a, b)
                    right = gate(1, c, d)
                    dirty = gate(0, left, right)
                    t_leaves = [line for line in neighbors[b] if line not in (c, d)]
                    s_leaves = [point for point in neighbors[c] if point not in (a, b)]
                    b_context = gate(1, dirty, fold(t_leaves)) if t_leaves else dirty
                    c_context = gate(1, dirty, fold(s_leaves)) if s_leaves else dirty
                    b_star = gate(0, b_context, b)
                    c_star = gate(0, c_context, c)
                    region = gate(1, b_star, c_star)
                    terms = [region]
                    for point in range(k):
                        if point == b:
                            continue
                        leaves = [line for line in neighbors[point] if line != c]
                        assert leaves
                        terms.append(gate(0, point, fold(leaves)))
                    output = fold(terms)
                    values = inputs.copy()
                    read_zero = inputs.copy()
                    read_one = inputs.copy()
                    violations = 0
                    dominated = []
                    for j, (op, u, v) in enumerate(gates):
                        x, y = values[u], values[v]
                        result = x | y if op else x & y
                        clean_u, clean_v = not (x & negative), not (y & negative)
                        violations += ((not op and (clean_u or clean_v))
                                       or (op and clean_u != clean_v))
                        for earlier, previous in enumerate(values):
                            if not ((result & positive) & ~previous) and not ((previous & negative) & ~result):
                                dominated.append([n + j, earlier])
                        values.append(result)
                        read_one.append((read_one[u] | read_one[v]) if op
                                        else (read_zero[u] & read_zero[v]))
                        read_zero.append((read_zero[u] | read_zero[v]) if op else 0)
                    assert values[output] == positive
                    assert len(gates) == 5 * k + 2
                    assert values[dirty] & negative
                    direct_uses = sum(u == dirty for _, u, _ in gates) + sum(v == dirty for _, _, v in gates)
                    assert direct_uses == 2
                    assert violations == 0
                    assert not dominated
                    seeds.append({
                        'centers': [b, c], 'outer_leaves': [a, d],
                        'T': t_leaves, 'S': s_leaves,
                        'dirty_and_wire': dirty, 'dirty_direct_uses': direct_uses,
                        'dirty_next_and_wires': [b_star, c_star],
                        'gates': gates, 'output': output, 'size': len(gates),
                        'normalization_violations': violations,
                        'dominated_gates': len(dominated),
                        'accepted_without_read1': (positive & ~read_one[output]).bit_count(),
                    })
    destination = root / (name + '-reused-dirty-seeds.json')
    destination.write_text(json.dumps(seeds, separators=(',', ':')) + '\n')
    print(json.dumps({
        'name': name, 'seeds': len(seeds), 'sizes': sorted({s['size'] for s in seeds}),
        'nonread1': sorted({s['accepted_without_read1'] for s in seeds}),
        'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
    }), flush=True)
