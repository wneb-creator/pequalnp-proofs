from collections import deque
from itertools import combinations, product
from pathlib import Path
import argparse
import json

parser = argparse.ArgumentParser(description='Audit an intermediate matrix obstruction, not L-meta-4970.')
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
OUT = args.output_dir
OUT.mkdir(parents=True, exist_ok=True)


def projective(v):
    first = next(x for x in v if x)
    return tuple((x * (1 if first == 1 else 2)) % 3 for x in v)


def symplectic(u, v):
    return (u[0]*v[2] - u[2]*v[0] + u[1]*v[3] - u[3]*v[1]) % 3


points = sorted({projective(v) for v in product(range(3), repeat=4) if any(v)})
point_id = {v: i for i, v in enumerate(points)}
line_sets = set()
for u, v in combinations(points, 2):
    if symplectic(u, v):
        continue
    line = frozenset(point_id[projective(tuple((a*x + b*y) % 3 for x, y in zip(u, v)))]
                     for a, b in product(range(3), repeat=2) if a or b)
    assert len(line) == 4
    line_sets.add(line)
lines = sorted(line_sets, key=lambda s: tuple(sorted(s)))
assert len(points) == len(lines) == 40
edges = sorted((p, j + 40) for j, line in enumerate(lines) for p in line)
edge_set = set(edges)
neighbors = [set() for _ in range(80)]
for a, b in edges:
    neighbors[a].add(b)
    neighbors[b].add(a)
assert len(edges) == 160 and all(len(s) == 4 for s in neighbors)
assert all(len(neighbors[a] & neighbors[b]) <= 1
           for side in [range(40), range(40, 80)] for a, b in combinations(side, 2))


def graph_girth():
    girth = 1000
    for start in range(80):
        dist = [-1]*80
        parent = [-1]*80
        dist[start] = 0
        q = deque([start])
        while q:
            v = q.popleft()
            for w in neighbors[v]:
                if dist[w] < 0:
                    dist[w] = dist[v]+1
                    parent[w] = v
                    q.append(w)
                elif parent[v] != w:
                    girth = min(girth, dist[v]+dist[w]+1)
        assert all(d >= 0 for d in dist)
    return girth


girth = graph_girth()
assert girth == 8
remaining = [set(s) for s in neighbors]
stack = [0]
tour = []
while stack:
    v = stack[-1]
    if remaining[v]:
        w = min(remaining[v])
        remaining[v].remove(w)
        remaining[w].remove(v)
        stack.append(w)
    else:
        tour.append(stack.pop())
tour.reverse()
assert len(tour) == 161 and tour[0] == tour[-1]
outgoing = [set() for _ in range(80)]
for a, b in zip(tour, tour[1:]):
    outgoing[a].add(b)
assert all(len(s) == 2 for s in outgoing)
classes = [{tuple(sorted((v, w))) for w in outgoing[v]} for v in range(80)]
assert set().union(*classes) == edge_set
assert sum(map(len, classes)) == len(edge_set)

gates = []
singletons = [frozenset([v]) for v in range(80)]
raw_reach = list(singletons)
pure = list(singletons)
edge_values = [sum(1 << i for i, e in enumerate(edges) if v in e) for v in range(80)]


def gate(op, a, b):
    assert 0 <= a < 80+len(gates) and 0 <= b < 80+len(gates)
    gates.append((op, a, b))
    if op == 'or':
        singletons.append(singletons[a] | singletons[b])
        raw_reach.append(raw_reach[a] | raw_reach[b])
        if pure[a] is not None and pure[b] is not None:
            pure.append(pure[a] | pure[b])
        else:
            assert not singletons[-1]
            pure.append(None)
        edge_values.append(edge_values[a] | edge_values[b])
    else:
        singletons.append(singletons[a] & singletons[b])
        raw_reach.append(frozenset())
        pure.append(None)
        edge_values.append(edge_values[a] & edge_values[b])
    return 79+len(gates)


def fold_gate(op, ws):
    ws = list(ws)
    assert ws
    ans = ws[0]
    for w in ws[1:]:
        ans = gate(op, ans, w)
    return ans


witness = [gate('or', *sorted(outgoing[v])) for v in range(80)]
rowcol = []
clause_starts = []
for v in range(80):
    opposite = set(range(40, 80)) if v < 40 else set(range(40))
    nonneighbors = sorted(opposite-neighbors[v])
    assert len(nonneighbors) == 36
    clauses = []
    for z in nonneighbors:
        candidates = [t for t in sorted(outgoing[v]) if not (neighbors[z] & neighbors[t])]
        assert candidates
        t = candidates[0]
        w = gate('or', z, t)
        clause_starts.append((v, z, t))
        w = gate('or', w, witness[v])
        for other in sorted(neighbors[v]-outgoing[v]):
            w = gate('or', w, other)
        assert pure[w] == neighbors[v] | {z}
        clauses.append(w)
    r = fold_gate('and', clauses)
    assert singletons[r] == neighbors[v]
    rowcol.append(gate('and', v, r))
    assert not singletons[rowcol[-1]]
U = fold_gate('or', rowcol[:40])
V = fold_gate('or', rowcol[40:])
output = gate('and', U, V)
assert edge_values[output] == (1 << 160)-1
assert all(edge_values[w] for w in range(80, 80+len(gates)))

negative_assignments = [set(range(40)), set(range(40, 80))]
for v in range(80):
    opposite = set(range(40, 80)) if v < 40 else set(range(40))
    negative_assignments.append({v} | (opposite-neighbors[v]))
assert all(not any(a in X and b in X for a, b in edges) for X in negative_assignments)
negative_values = [sum(1 << j for j, X in enumerate(negative_assignments) if v in X)
                   for v in range(80)]
for op, a, b in gates:
    negative_values.append((negative_values[a] | negative_values[b]) if op == 'or'
                           else (negative_values[a] & negative_values[b]))
assert negative_values[output] == 0
assert all(negative_values[w] for w in range(80, output))

star_or = []
bad_or = []
for j, (op, a, b) in enumerate(gates):
    if op != 'or':
        continue
    w = 80+j
    assert not raw_reach[w] or len({int(v >= 40) for v in raw_reach[w]}) == 1
    if not singletons[a] or not singletons[b] or len({int(v >= 40) for v in singletons[w]}) > 1:
        bad_or.append(j)
    if pure[w] is not None and len(pure[w]) >= 2:
        common = set(range(80))
        for leaf in pure[w]:
            common &= neighbors[leaf]
        if common:
            assert len(common) == 1
            star_or.append((j, next(iter(common)), sorted(pure[w])))
assert [j for j, _, _ in star_or] == list(range(80))
assert len(bad_or) == 78
for a, b in edges:
    assert sum((center == a and b in leaves) or (center == b and a in leaves)
               for _, center, leaves in star_or) == 1

for a in range(40):
    for b in range(40, 80):
        cell = edge_values[rowcol[a]] & edge_values[rowcol[b]]
        assert cell == (1 << edges.index((a, b)) if (a, b) in edge_set else 0)

rectangle_sizes = []
rectangle_witnesses = []
for a in range(40):
    for b in range(40, 80):
        if (a, b) in edge_set:
            continue
        rect = [(x, y) for x, y in edges if x not in neighbors[b] and y not in neighbors[a]]
        assert rect
        rectangle_sizes.append(len(rect))
        rectangle_witnesses.append([a, b, *rect[0]])
assert set(rectangle_sizes) == {129}

and_count = sum(op == 'and' for op, _, _ in gates)
or_count = len(gates)-and_count
assert (len(gates), and_count, or_count) == (14559, 2881, 11678)
summary = {
    'geometry': 'W(3,3), projective points in F3^4 and totally isotropic 2-spaces',
    'point_count': 40, 'line_count': 40, 'degree': 4, 'edges': 160,
    'girth': girth, 'connected': True, 'C4_free': True,
    'euler_outdegrees': sorted(set(map(len, outgoing))),
    'witness_classes': 80, 'witness_class_size': 2,
    'witness_overlap_components': 80,
    'only_star_or_gates': len(star_or), 'served': True, 'T0': True,
    'each_edge_exactly_one_serving_root': True,
    'every_actual_gate_edge_active': True,
    'only_output_gate_below_F': True,
    'explicit_independent_assignments_certifying_other_gates_not_below_F': len(negative_assignments),
    'total_gates': len(gates), 'and_gates': and_count, 'or_gates': or_count,
    'semantic_bad_or_gates': len(bad_or),
    'matrix_active_cells': 160, 'each_active_cell_singleton_edge': True,
    'active_graph_vertices': 80, 'active_graph_rank': 79,
    'witness_labels': 80, 'rank_deficit': 1,
    'nonedge_complement_rectangles': len(rectangle_sizes),
    'rectangle_edge_count_min': min(rectangle_sizes),
    'rectangle_edge_count_max': max(rectangle_sizes),
    'exact_output_argument': 'CNF distributivity and every nonedge complement rectangle has an edge; not an exhaustive 2^80 truth table',
    'scope': 'Intermediate active-matrix rainbow-forest and bad-OR count obstructions only; no full-gap refutation'
}
(OUT/'independent-gq-audit.json').write_text(json.dumps(summary, indent=2)+'\n')
(OUT/'independent-gq-certificate.json').write_text(json.dumps({
    'points': points, 'lines': [sorted(s) for s in lines], 'edges': edges,
    'outgoing': [sorted(s) for s in outgoing], 'star_or': star_or,
    'clause_starts': clause_starts, 'complement_rectangle_witnesses': rectangle_witnesses,
    'gates': gates, 'output': output, 'rowcol_wires': rowcol
}, separators=(',', ':'))+'\n')
print(json.dumps(summary, indent=2))
