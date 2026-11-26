from itertools import combinations, product
from pathlib import Path
import argparse
import json

parser = argparse.ArgumentParser(description='Audit an intermediate augmented-component obstruction.')
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
OUT = args.output_dir
OUT.mkdir(parents=True, exist_ok=True)


def projective(v):
    first = next(x for x in v if x)
    inverse = pow(first, -1, 5)
    return tuple(x*inverse % 5 for x in v)


points = sorted({projective(v) for v in product(range(5), repeat=3) if any(v)})
lines = list(points)
assert len(points) == len(lines) == 31
edges = [(a, 31+b) for a, p in enumerate(points) for b, line in enumerate(lines)
         if sum(x*y for x, y in zip(p, line)) % 5 == 0]
neighbors = [set() for _ in range(62)]
for a, b in edges:
    neighbors[a].add(b)
    neighbors[b].add(a)
assert len(edges) == 186 and all(len(N) == 6 for N in neighbors)
assert all(len(neighbors[a] & neighbors[b]) == 1
           for side in [range(31), range(31, 62)] for a, b in combinations(side, 2))
edge_masks = [(1 << a) | (1 << b) for a, b in edges]


def minimal(terms):
    answer = []
    for term in sorted(set(terms), key=lambda m: (m.bit_count(), m)):
        if not any(other & term == other for other in answer):
            answer.append(term)
    return answer


gates = []
dnf = [[1 << v] for v in range(62)]
raw = [1 << v for v in range(62)]


def gate(op, a, b):
    assert 0 <= a < 62+len(gates) and 0 <= b < 62+len(gates)
    gates.append((op, a, b))
    dnf.append(minimal(dnf[a]+dnf[b]) if op == 'or'
               else minimal(x | y for x in dnf[a] for y in dnf[b]))
    raw.append((raw[a] | raw[b]) if op == 'or' else 0)
    return 61+len(gates)


def fold(op, values):
    values = list(values)
    answer = values[0]
    for v in values[1:]:
        answer = gate(op, answer, v)
    return answer


buffers = {b: gate('and', b, b) for b in range(31, 62)}
pair_roots = []
for a in range(31):
    N = sorted(neighbors[a])
    pair_roots.append([gate('or', buffers[N[i]], buffers[N[i+1]]) for i in range(0, 6, 2)])
c = 0
Qc = fold('or', pair_roots[c])
H = fold('and', [gate('or', c, buffers[b]) for b in sorted(neighbors[c])])
K = gate('and', H, Qc)
anchor_product = sum(1 << b for b in neighbors[c])
assert dnf[H] == minimal([1 << c, anchor_product])
assert dnf[K] == minimal([(1 << c) | (1 << b) for b in neighbors[c]]+[anchor_product])
A = []
R = []
for a in range(31):
    Ra = fold('or', [K]+pair_roots[a])
    R.append(Ra)
    A.append(gate('and', a, Ra))
output = fold('or', A)
assert set(dnf[output]) == set(edge_masks)

def vertices(mask):
    return [v for v in range(62) if mask >> v & 1]


pure_or = []
eligible = []
bad_or = []
safe_and = []
singleton = [sum(m for m in terms if m.bit_count() == 1) for terms in dnf]
for j, (op, a, b) in enumerate(gates):
    w = 62+j
    assert any(any(term & e == term for term in dnf[w]) for e in edge_masks)
    below = all(any(e & term == e for e in edge_masks) for term in dnf[w])
    if op == 'and' and below:
        safe_and.append(w)
    if op != 'or':
        continue
    assert raw[w].bit_count() <= 1
    support = singleton[w]
    if singleton[a] == 0 or singleton[b] == 0 or len({v >= 31 for v in vertices(support)}) > 1:
        bad_or.append(j)
    if all(term.bit_count() == 1 for term in dnf[w]):
        Q = vertices(support)
        pure_or.append((j, Q))
        if len(Q) >= 2:
            centers = set(range(62))
            for q in Q:
                centers &= neighbors[q]
            if centers:
                assert len(centers) == 1
                eligible.append((j, next(iter(centers)), Q))
assert len(pure_or) == 102 and len(eligible) == 96
assert safe_and == A
assert len(bad_or) == 67

parent = list(range(186))
edge_id = {e: i for i, e in enumerate(edges)}


def root(i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i


served = set()
for j, center, Q in eligible:
    owned = [edge_id[tuple(sorted((center, q)))] for q in Q]
    served.update(owned)
    for e in owned[1:]:
        parent[root(e)] = root(owned[0])
assert len(served) == 186
components = {}
for e in range(186):
    components.setdefault(root(e), []).append(e)
assert sorted(map(len, components.values())) == [2]*90+[6]

reachable = set()
stack = [output]
while stack:
    w = stack.pop()
    if w in reachable:
        continue
    reachable.add(w)
    if w >= 62:
        _, a, b = gates[w-62]
        stack.extend([a, b])
assert all(w in reachable for w in range(62, output+1))
assert all(op != 'and' for op, a, b in gates if a in A or b in A)
ands = sum(op == 'and' for op, _, _ in gates)
ors = len(gates)-ands
assert (ands, ors, len(gates)) == (68, 224, 292)
summary = {
    'geometry': 'PG(2,5), independent projective-coordinate construction',
    'point_count': 31, 'line_count': 31, 'degree': 6, 'edge_count': 186,
    'C4_free': True, 'unique_intersection_of_two_points_or_two_lines': True,
    'and_count': ands, 'or_count': ors, 'size': len(gates),
    'pure_or_roots': len(pure_or), 'eligible_star_or_roots': len(eligible),
    'eligible_pair_roots': 93, 'additional_anchor_star_roots': 3,
    'semantic_witness_components': len(components),
    'augmented_semantic_and_raw_components': len(components),
    'component_sizes': {'2': 90, '6': 1},
    'maximum_raw_or_support_size': max(raw[62+j].bit_count() for j, (op, _, _) in enumerate(gates) if op == 'or'),
    'semantic_bad_or_count': len(bad_or),
    'every_gate_output_reachable': True, 'every_gate_edge_active': True,
    'safe_AND_gates': len(safe_and), 'safe_AND_gates_exactly_Aa': True,
    'no_safe_AND_below_another_AND': True,
    'served': True, 'T0': True,
    'output_minimal_DNF_equals_exact_186_edges': True,
    'verification_method': 'exact minimal monotone DNFs, not a 2^62 truth-table claim',
    'component_minus_AND_deficit': len(components)-ands,
    'full_gap_cover': 'all 31 point vertices; 186+31=217 <= 292+1=293',
    'scope': 'Refutes augmented-witness-components<=AND for this nonminimal circuit only; not the full gap'
}
(OUT/'independent-pg5-audit.json').write_text(json.dumps(summary, indent=2)+'\n')
(OUT/'independent-pg5-certificate.json').write_text(json.dumps({
    'points': points, 'lines': lines, 'edges': edges, 'gates': gates,
    'output': output, 'minimal_DNFs': dnf, 'raw_OR_supports': raw,
    'eligible_OR_roots': eligible, 'component_edges': list(components.values()),
    'A_wires': A, 'R_wires': R, 'H_wire': H, 'K_wire': K, 'Qc_wire': Qc
}, separators=(',', ':'))+'\n')
print(json.dumps(summary, indent=2))
