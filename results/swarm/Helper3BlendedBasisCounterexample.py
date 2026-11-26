"""Full-truth check of a nonminimum blended-basis obstruction.

This is not a counterexample to L-meta-4970. It shows that a spanning
forest labelled by productive blended ORs cannot always avoid every
mixed-semantic OR gate. Run with Python 3; only JSON is written to stdout.
"""

import itertools
import json

n, p = 6, 2
names = ['z', 'q', 'b', 'c', 'd', 'e']
Q = {2, 3, 4, 5}
edges = {(0, b) for b in Q}
gates = [
    ('and', 1, 1),       # wire 6: qbuf
    ('or', 2, 6),        # wire 7: g
    ('or', 3, 7),        # wire 8: h
    ('or', 2, 4),        # wire 9: r
    ('or', 3, 5),        # wire 10: s
    ('and', 0, 2),       # wire 11: zb
    ('and', 0, 3),       # wire 12: zc
    ('and', 0, 4),       # wire 13: zd
    ('and', 0, 5),       # wire 14: ze
    ('or', 11, 12),      # wire 15
    ('or', 13, 14),      # wire 16
    ('or', 15, 16),      # wire 17: output
]
output = n + len(gates) - 1
table = []
for mask in range(1 << n):
    values = [bool(mask >> v & 1) for v in range(n)]
    for j, (op, a, b) in enumerate(gates):
        assert 0 <= a < n + j and 0 <= b < n + j
        values.append(values[a] and values[b] if op == 'and' else values[a] or values[b])
    target = any(values[a] and values[b] for a, b in edges)
    assert values[output] == target
    table.append(values)

raw = [{v} for v in range(n)]
for op, a, b in gates:
    support = raw[a] | raw[b] if op == 'or' else set()
    if op == 'or':
        assert not (any(v < p for v in support) and any(v >= p for v in support))
    raw.append(support)
semantic = [{v for v in range(n) if table[1 << v][w]} for w in range(output + 1)]
safe = [all(not row[w] or any(row[v] for v in Q) for row in table)
        for w in range(output + 1)]
blended = [semantic[w] if safe[w] else raw[w] for w in range(output + 1)]
admissible = [raw[w] <= Q for w in range(output + 1)]
charged = [w for w in range(n, output + 1)
           if admissible[w] and gates[w - n][0] == 'or' and len(blended[w]) >= 2]
carriers = {w: [a for a in range(w) if admissible[a] and blended[w] <= blended[a]]
            for w in range(output + 1)}
productive = [w for w in charged if not carriers[w]]
bad = [w for w in range(n, output + 1) if gates[w - n][0] == 'or'
       and any(v < p for v in semantic[w]) and any(v >= p for v in semantic[w])]
assert charged == productive == [8, 9, 10]
assert bad == [7, 8]
assert [blended[w] for w in productive] == [{2, 3}, {2, 4}, {3, 5}]
assert raw[8] == {2, 3} and semantic[8] == {1, 2, 3}
assert not safe[8]

pure_witnesses = []
served = set()
for w in range(n, output + 1):
    if gates[w - n][0] != 'or':
        continue
    support = semantic[w]
    if len(support) < 2:
        continue
    if not all(row[w] == any(row[v] for v in support) for row in table):
        continue
    if support <= Q:
        pure_witnesses.append((w, sorted(support)))
        served.update((0, v) for v in support)
assert pure_witnesses == [(9, [2, 4]), (10, [3, 5])]
assert served == edges
assert all(sum((a, b) in edges and (aa, b) in edges for b in range(p, n)) <= 1
           for a in range(p) for aa in range(a + 1, p))

def components(labels):
    groups = [{v} for v in Q]
    for w in labels:
        assert len(blended[w]) == 2
        u, v = sorted(blended[w])
        left = next(group for group in groups if u in group)
        right = next(group for group in groups if v in group)
        if left != right:
            groups.remove(left)
            groups.remove(right)
            groups.append(left | right)
    return sorted([sorted(group) for group in groups])

eligible_trees = [list(labels) for labels in itertools.combinations(productive, len(Q) - 1)
                  if len(components(labels)) == 1]
assert eligible_trees == [[8, 9, 10]]
assert components([9, 10]) == [[2, 4], [3, 5]]
assert all(set(labels) & set(bad) for labels in eligible_trees)
assert all(len(blended[w]) < 2 for w in range(output + 1) if w not in productive)

report = dict(
    status='PASS', scope='nonminimum circuit; refutes exclusion of all mixed-semantic ORs from every augmented productive blended basis',
    inputs=names, p=p, l=n-p, gates=gates, output=output,
    edges=sorted((a, b - p) for a, b in edges), global_vertex_edges=sorted(edges),
    assignments_checked=1 << n,
    IsAO2=True, T0=True, exact_edge_function=True, C4_free=True,
    all_edges_served=True, pure_witnesses=pure_witnesses,
    full_Q=sorted(Q), charged=charged, productive=productive,
    mixed_semantic_bad_ORs=bad, mandatory_bad_label=8,
    eligible_labelled_trees=eligible_trees,
    components_without_bad_label=components([9, 10]),
    support_table=[dict(wire=w, name=names[w] if w < n else None,
                        raw=sorted(raw[w]), semantic=sorted(semantic[w]), safe=safe[w],
                        blended=sorted(blended[w]), admissible=admissible[w],
                        earlier_carriers=carriers[w]) for w in range(output + 1)],
    full_gap_counterexample=False,
)
print(json.dumps(report, indent=2))
