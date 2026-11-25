import itertools
import json

q = 5


def normalise(v):
    first = next(a for a in v if a)
    inv = pow(first, -1, q)
    return tuple(a * inv % q for a in v)


vertices = sorted({normalise(v) for v in itertools.product(range(q), repeat=3) if any(v)})
v = len(vertices)
edges = {(i, j) for i, a in enumerate(vertices) for j, b in enumerate(vertices)
         if sum(x * y for x, y in zip(a, b)) % q == 0}
neighbours = [{j for i2, j in edges if i2 == i} for i in range(v)]
assert v == 31 and len(edges) == 186
assert all(len(row) == 6 for row in neighbours)
assert all(len(neighbours[i] & neighbours[j]) == 1 for i in range(v) for j in range(i + 1, v))

mate = {}


def augment(i, seen):
    for j in sorted(neighbours[i]):
        if j in seen:
            continue
        seen.add(j)
        if j not in mate or augment(mate[j], seen):
            mate[j] = i
            return True
    return False


assert all(augment(i, set()) for i in range(v))
matching = sorted((i, j) for j, i in mate.items())
assert len(matching) == v
assert len({i for i, _ in matching}) == v
assert len({j for _, j in matching}) == v
assert set(matching) <= edges

n = 2 * v
gates = []


def gate(op, a, b):
    out = n + len(gates)
    assert a < out and b < out
    gates.append((op, a, b))
    return out


def big_or(wires):
    wires = list(wires)
    out = wires[0]
    for wire in wires[1:]:
        out = gate('or', out, wire)
    return out


all_points = big_or(range(v))
all_lines = big_or(range(v, n))
point_masks = [gate('and', i, all_lines) for i in range(v)]
line_masks = [gate('and', all_points, v + j) for j in range(v)]
stars = [gate('and', point_masks[i], big_or(line_masks[j] for j in sorted(neighbours[i])))
         for i in range(v)]
output = big_or(stars)

# The exact identity below proves that replacing a point/line by these masks
# preserves every edge term, for arbitrary simultaneous input assignments.
for a, b, any_point, any_line in itertools.product([False, True], repeat=4):
    if (not a or any_point) and (not b or any_line):
        assert ((a and any_line) and (any_point and b)) == (a and b)

supports = [{i} for i in range(n)]
or_reach = [{i} for i in range(n)]
merges = []
positive_slots = []
zero_gates = []
zero_slots = 0
for k, (op, a, b) in enumerate(gates):
    support = supports[a] | supports[b] if op == 'or' else supports[a] & supports[b]
    reach = or_reach[a] | or_reach[b] if op == 'or' else set()
    assert not (any(i < v for i in reach) and any(i >= v for i in reach))
    if op == 'and':
        assert not support
        positive_slots.extend((k, w) for w in {a, b} if supports[w])
    elif len(support) > 1 and all(supports[w] for w in {a, b}) and a != b:
        merges.append(k)
    zero_slots += sum(1 for w in {a, b} if w >= n and not supports[w])
    if not support:
        zero_gates.append(k)
    supports.append(support)
    or_reach.append(reach)

reachable = set()


def visit(w):
    if w < n or w - n in reachable:
        return
    k = w - n
    reachable.add(k)
    _, a, b = gates[k]
    visit(a)
    visit(b)


visit(output)
assert len(reachable) == len(gates)
assert len(gates) == 338
assert len(positive_slots) == 124 and len(merges) == 60
assert len(zero_gates) == 278 and zero_slots == 432
assert zero_slots - len(zero_gates) + 1 == 155
assert len(positive_slots) + len(merges) == 184 < len(edges) + len(matching) == 217

print(json.dumps({
    'status': 'Exact Python arithmetic and finite identities checked; not Lean checked',
    'purpose': 'Excludes E+cover <= positive AND slots + positive OR merges; does not refute L-meta-4675',
    'field_order': q,
    'vertices_each_colour': v,
    'edges': len(edges),
    'matching_cardinality': len(matching),
    'vertex_cover_cardinality': v,
    'edge_plus_minimum_cover': len(edges) + v,
    'masked_circuit_gates': len(gates),
    'positive_AND_slots': len(positive_slots),
    'positive_OR_merges': len(merges),
    'positive_boundary_budget': len(positive_slots) + len(merges),
    'zero_support_gates': len(zero_gates),
    'zero_support_incoming_slots': zero_slots,
    'zero_support_reconvergence': zero_slots - len(zero_gates) + 1,
    'tCount': 0,
    'all_AND_singleton_false': True,
    'matching': matching,
    'normalised_projective_points': vertices,
}, indent=2))
