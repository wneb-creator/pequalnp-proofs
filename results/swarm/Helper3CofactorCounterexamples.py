"""Check two stronger-cofactor obstructions; neither refutes gap L-meta-4970.

Run with Python 3.8 or newer. Uses only the standard library and writes no files.
Every bit of a truth-table integer represents one Boolean input assignment.
The examples have 18 variables, so all 262144 assignments are checked exactly.
"""

import itertools
import json


def build_example(absorbed_term):
    p = l = 9
    n = p + l
    pairs = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    edges = {(a, b) for a, pair in enumerate(pairs) for b in pair}
    edges.update((a, 4 + a) for a in range(5))
    edges.update((5 + b, b) for b in range(4))
    cycle = [5, 0, 7, 2, 6, 3, 8, 1]
    orientation = list(zip(cycle, cycle[1:] + cycle[:1])) + [(7, 4), (4, 8)]

    def center(u):
        return u if u < 5 else p + u - 5

    def private_leaf(u):
        return p + 4 + u if u < 5 else u

    oriented_edges = {
        (min(center(u), center(v)), max(center(u), center(v)) - p)
        for u, v in orientation
    }
    assert oriented_edges == {(a, b) for a, pair in enumerate(pairs) for b in pair}
    gates = []

    def add_gate(op, a, b):
        gates.append((op, min(a, b), max(a, b)))
        return n + len(gates) - 1

    terms = []
    internal_roots = {}
    for u in range(9):
        outgoing = [center(v) for a, v in orientation if a == u]
        assert outgoing
        root = outgoing[0]
        for v in outgoing[1:]:
            root = add_gate('or', root, v)
        internal_roots[u] = root
        root = add_gate('or', root, private_leaf(u))
        terms.append(add_gate('and', center(u), root))
    output = terms[0]
    for term in terms[1:]:
        output = add_gate('or', output, term)
    if absorbed_term:
        redundant = add_gate('and', center(7), internal_roots[7])
        output = add_gate('or', output, redundant)
    return p, l, edges, gates, output


def input_truth_tables(n):
    assert n >= 3
    byte_count = (1 << n) // 8
    tables = []
    for i in range(n):
        if i < 3:
            raw = bytes([(0xaa, 0xcc, 0xf0)[i]]) * byte_count
        else:
            block = 1 << (i - 3)
            raw = (bytes(block) + bytes([255]) * block) * (byte_count // (2 * block))
        tables.append(int.from_bytes(raw, 'little'))
    return tables


def cofactor_counts(n, gates, output, cover):
    values = [v not in cover for v in range(n)]
    pointers = [None if value else v for v, value in enumerate(values)]
    dependencies = {}
    removed = 0
    for g, (op, a, b) in enumerate(gates):
        removed += bool(values[a] or values[b])
        values.append(values[a] or values[b] if op == 'or' else values[a] and values[b])
        aa, bb = pointers[a], pointers[b]
        if op == 'or' and (aa is None or bb is None):
            pointer = None
        elif op == 'and' and aa is None:
            pointer = bb
        elif op == 'and' and bb is None:
            pointer = aa
        else:
            pointer = n + g
            dependencies[pointer] = (aa, bb)
        pointers.append(pointer)
    assert not values[output]
    visited = set()
    stack = [pointers[output]]
    while stack:
        wire = stack.pop()
        assert wire is not None
        if wire < n or wire in visited:
            continue
        visited.add(wire)
        stack.extend(dependencies[wire])
    return removed, len(gates) - len(visited)


def verify_example(absorbed_term):
    p, l, edges, gates, output = build_example(absorbed_term)
    n = p + l
    assert len(edges) == 19
    assert all(sum((a, b) in edges and (aa, b) in edges for b in range(l)) <= 1
               for a in range(p) for aa in range(a + 1, p))
    inputs = input_truth_tables(n)
    tables = list(inputs)
    reach = [1 if v < p else 2 for v in range(n)]
    for g, (op, a, b) in enumerate(gates):
        assert op in ('and', 'or') and 0 <= a < n + g and 0 <= b < n + g
        tables.append(tables[a] | tables[b] if op == 'or' else tables[a] & tables[b])
        colors = reach[a] | reach[b] if op == 'or' else 0
        assert colors != 3
        reach.append(colors)
    target = 0
    for a, b in edges:
        target |= inputs[a] & inputs[p + b]
    assert tables[output] == target

    neighbors = [{p + b for a, b in edges if a == u} if u < p else
                 {a for a, b in edges if p + b == u} for u in range(n)]
    available = set()
    served = set()
    for g, (op, _, _) in enumerate(gates):
        if op != 'or':
            continue
        support = {v for v in range(n) if tables[n + g] >> (1 << v) & 1}
        if len(support) < 2:
            continue
        pure_or = 0
        for v in support:
            pure_or |= inputs[v]
        if pure_or != tables[n + g]:
            continue
        for u in range(n):
            if support <= neighbors[u]:
                available.add(u)
                served.update((u, v - p) if u < p else (v, u - p) for v in support)
    assert served == edges
    assert available == set(range(5)) | set(range(9, 13))

    covers = []
    for size in range(n + 1):
        for chosen in itertools.combinations(range(n), size):
            cover = set(chosen)
            if not all(a in cover or p + b in cover for a, b in edges):
                continue
            complement = set(range(n)) - cover
            if not all(neighbors[v] & complement for v in cover):
                continue
            raw, pruned = cofactor_counts(n, gates, output, cover)
            covers.append(dict(cover=list(chosen),raw_removed=raw,pruned_removed=pruned))
    assert len(covers) == 72 and all(len(c['cover']) == 9 for c in covers)
    eligible = [c for c in covers if set(c['cover']) <= available]
    assert len(eligible) == 1 and set(eligible[0]['cover']) == available
    max_raw = max(c['raw_removed'] for c in covers)
    max_pruned = max(c['pruned_removed'] for c in covers)
    assert (len(gates), max_raw, max_pruned) == ((29, 19, 19) if absorbed_term else (27, 18, 19))
    assert (eligible[0]['raw_removed'],eligible[0]['pruned_removed']) == ((18,18) if absorbed_term else (18,19))
    return dict(gates=len(gates),edges=len(edges),assignments_checked=1 << n,
                C4_free=True,T0=True,all_edges_served=True,exact_available=sorted(available),
                minimum_vertex_cover=9,original_bound_holds=len(gates) >= len(edges) + 9 - 1,
                minimal_covers=len(covers),available_cover=eligible[0],
                unrestricted_max_raw=max_raw,unrestricted_max_pruned=max_pruned,
                unrestricted_pruned_maximizer=next(c for c in covers if c['pruned_removed'] == max_pruned))


def main():
    results = {'27_gate': verify_example(False), '29_gate': verify_example(True)}
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
