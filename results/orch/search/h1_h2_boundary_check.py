"""Finite checks for a conditional H1/H2 route; no plane circuit is found here."""
import json
from collections import Counter


def plane_check():
    n = 13
    full = (1 << n) - 1
    differences = {0, 1, 3, 9}
    neighbors = [sum(1 << l for l in range(n) if (p - l) % n in differences)
                 for p in range(n)]
    touched = [0] * (1 << n)
    for points in range(1, 1 << n):
        bit = points & -points
        touched[points] = touched[points ^ bit] | neighbors[bit.bit_length() - 1]
    maximal = []
    for points in range(1 << n):
        lines = full ^ touched[points]
        closure = sum(1 << p for p in range(n) if not neighbors[p] & lines)
        if closure == points:
            maximal.append(points | (lines << n))
    mixed = [mask for mask in maximal if mask & full and mask >> n]
    assert len(maximal) == 704 and len(mixed) == 702
    singleton_covers = [sum(bool(mask & (1 << i)) for mask in mixed) for i in range(2*n)]
    assert min(singleton_covers) > 0
    # Every nonempty point set with some allowed line extends to a mixed
    # maximal independent set. Taking all currently allowed lines suffices.
    extensions_checked = 0
    for points in range(1, 1 << n):
        lines = full ^ touched[points]
        if lines:
            closure = sum(1 << p for p in range(n) if not neighbors[p] & lines)
            assert points & closure == points
            assert closure | (lines << n) in mixed
            extensions_checked += 1
    blocking = [points for points in range(1 << n) if touched[points] == full]
    minimal_blocking = [points for points in blocking
                        if all(touched[points ^ (1 << p)] != full
                               for p in range(n) if points & (1 << p))]
    return dict(maximal_independent_sets=len(maximal),
                mixed_maximal_independent_sets=len(mixed),
                singleton_mixed_extension_counts=singleton_covers,
                nonempty_point_sets_with_mixed_extension=extensions_checked,
                blocking_point_subsets=len(blocking),
                minimal_blocking_point_set_sizes=dict(sorted(Counter(
                    points.bit_count() for points in minimal_blocking).items())),
                plane_h1_circuit_constructed=False)


def matching_check():
    # Inputs p,q,l,m. Target edges pm and ql.
    gates = [(0, 0, 2), (0, 1, 3), (1, 4, 5),
             (0, 0, 1), (0, 2, 3), (1, 7, 8), (1, 6, 9)]
    edges = [(0, 3), (1, 2)]
    def evaluate(mask):
        values = [bool(mask & (1 << i)) for i in range(4)]
        for op, a, b in gates:
            assert a != b and max(a, b) < len(values)
            values.append((values[a] and values[b]) if op else
                          (values[a] or values[b]))
        return values
    for mask in range(16):
        expected = any(mask & (1 << a) and mask & (1 << b) for a,b in edges)
        assert evaluate(mask)[-1] == bool(expected)
    mixed_maximal = [(1 << 0) | (1 << 2), (1 << 1) | (1 << 3)]
    assert all(not evaluate(mask)[6] for mask in mixed_maximal)
    assert all(evaluate((1 << a) | (1 << b))[6] for a,b in edges)
    assert evaluate(3)[6] and evaluate(12)[6]
    for i in range(4):
        assert not evaluate(1 << i)[6] and not evaluate(1 << i)[9]
    derivatives = []
    for a,b in edges:
        pair = []
        for base,seed in [(a,b), (b,a)]:
            values = evaluate(1 << base)
            d = [i == seed for i in range(4)]
            for op,x,y in gates:
                d.append(((values[x] and d[y]) or (d[x] and values[y]))
                         if op else (d[x] or d[y]))
            assert not d[-1]
            pair.append(d[-1])
        derivatives.append(pair)
    return dict(inputs=4, gates=gates, h1_wire=6, h2_wire=9, output=10,
                truth_assignments_checked=16, mixed_maximal_independent_sets=2,
                edges=edges, directional_derivatives=derivatives)


if __name__ == '__main__':
    print(json.dumps(dict(plane=plane_check(), matching_control=matching_check()), indent=2))
