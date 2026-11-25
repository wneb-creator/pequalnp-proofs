import json


def build(r):
    n = 2 * r + 1
    gates = []
    cache = {}

    def gate(op, a, b):
        a, b = sorted((a, b))
        key = (op, a, b)
        if key not in cache:
            cache[key] = n + len(gates)
            gates.append(key)
        return cache[key]

    def combine(op, wires):
        result = wires[0]
        for w in wires[1:]:
            result = gate(op, result, w)
        return result

    points = [gate('and', i, i) for i in range(r + 1)]
    clauses = []
    for choice in range(1, 1 << r):
        inputs = [points[0]] + [points[i + 1] if choice >> i & 1 else r + i + 1 for i in range(r)]
        clauses.append(combine('or', inputs))
    dirty = combine('and', clauses)
    lines = combine('or', list(range(r + 1, 2 * r + 1)))
    output = gate('and', dirty, lines)
    edges = [(0, r + i + 1) for i in range(r)] + [(i + 1, r + i + 1) for i in range(r)]
    return n, gates, output, dirty, edges


def verify(r):
    n, gates, output, dirty, edges = build(r)
    rows = 1 << n
    values = [sum(1 << x for x in range(rows) if x >> i & 1) for i in range(n)]
    colours = [1 if i <= r else 2 for i in range(n)]
    ancestors = [0] * n
    for j, (op, a, b) in enumerate(gates):
        assert a < n + j and b < n + j
        values.append(values[a] & values[b] if op == 'and' else values[a] | values[b])
        colours.append(0 if op == 'and' else colours[a] | colours[b])
        ancestors.append(ancestors[a] | ancestors[b] | (1 << j))
    target = sum(1 << x for x in range(rows) if any(x >> a & 1 and x >> b & 1 for a, b in edges))
    assert values[output] == target
    assert all(c != 3 for c in colours)
    clean_ands = [j for j, (op, _, _) in enumerate(gates) if op == 'and' and not (values[n + j] & ~target)]
    assert clean_ands == [output - n]
    assert all(not (ancestors[n + j] >> k & 1) for j, (op, _, _) in enumerate(gates) if op == 'and' for k in clean_ands if k != j)
    assert gates[dirty - n][0] == 'and' and values[dirty] & ~target
    assert all(j <= dirty - n for j, (op, _, _) in enumerate(gates) if op == 'and' and j != output - n)
    assert colours[dirty] == 0
    assert all(sum((a, b) in edges and (a2, b) in edges for b in range(r + 1, n)) <= 1
               for a in range(r + 1) for a2 in range(a + 1, r + 1))
    for kill in range(len(gates)):
        vals = [sum(1 << k for k, (a, b) in enumerate(edges) if i == a or i == b) for i in range(n)]
        for j, (op, a, b) in enumerate(gates):
            vals.append(0 if j == kill else (vals[a] & vals[b] if op == 'and' else vals[a] | vals[b]))
        assert vals[output] != (1 << len(edges)) - 1
    return dict(r=r, inputs=n, gates=len(gates), edges=len(edges), vertex_cover=r,
                only_clean_and=output - n, last_dirty_and=dirty - n,
                residual_edges=len(edges), all_gates_edge_pivotal=True,
                t_count=0, top_form=True, full_truth_table_verified=True)


if __name__ == '__main__':
    for r in range(2, 6):
        print(json.dumps(verify(r), sort_keys=True), flush=True)
