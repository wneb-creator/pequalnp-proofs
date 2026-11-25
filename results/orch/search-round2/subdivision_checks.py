"""Finite checks for the double-subdivision research route; no proof certificate."""

from itertools import combinations


def accepts(edges, mask):
    return any(mask >> u & 1 and mask >> v & 1 for u, v in edges)


def cover_number(n, edges):
    best = n
    for mask in range(1 << n):
        if mask.bit_count() < best and all(mask >> u & 1 or mask >> v & 1 for u, v in edges):
            best = mask.bit_count()
    return best


def check(name, n, edges):
    m = len(edges)
    N = n + 2 * m
    subdivided = []
    for e, (u, v) in enumerate(edges):
        a, b = n + 2 * e, n + 2 * e + 1
        subdivided.extend([(u, a), (a, b), (b, v)])
    tau = cover_number(n, edges)
    tau_subdivided = cover_number(N, subdivided)
    assert tau_subdivided == m + tau
    failures = 0
    for mask in range(1 << N):
        h = accepts(subdivided, mask)
        g = accepts(edges, mask)
        rectangles = any(
            (mask >> u & 1 or mask >> (n + 2 * e + 1) & 1)
            and (mask >> v & 1 or mask >> (n + 2 * e) & 1)
            for e, (u, v) in enumerate(edges)
        )
        assert rectangles == (h or g)
        auxiliaries_present = bool(mask >> n)
        failures += bool(rectangles and auxiliaries_present and not h)
    obstructed = 0
    if tau >= 3:
        h_edges = {frozenset(e) for e in subdivided}
        for T in combinations(range(N), 2):
            if frozenset(T) in h_edges:
                continue
            neighbors = {
                u for u in range(n)
                if any(frozenset((u, t)) in h_edges for t in T)
            }
            assert len(neighbors) <= 2
            u, v = next((u, v) for u, v in edges if u not in neighbors and v not in neighbors)
            witness = sum(1 << t for t in set(T) | {u, v})
            assert not accepts(subdivided, witness)
            assert accepts(edges, witness)
            assert accepts([T], witness)
            obstructed += 1
    print({
        "base": name,
        "vertices": n,
        "edges": m,
        "vertex_cover": tau,
        "subdivision_vertices": N,
        "subdivision_edges": len(subdivided),
        "subdivision_vertex_cover": tau_subdivided,
        "canonical_gate_count": len(subdivided) + tau_subdivided - 1,
        "full_truth_table_rows": 1 << N,
        "rectangle_identity": "PASS",
        "auxiliary_OR_guard_false_positives": failures,
        "excluded_extra_quadratic_guard_edges": obstructed,
    }, flush=True)


check("K3", 3, list(combinations(range(3), 2)))
check("K2,2", 4, [(u, v) for u in (0, 1) for v in (2, 3)])
check("K4", 4, list(combinations(range(4), 2)))
