"""Exhaustive check of a normalized, nonleast two-junk core on the path P5.

This refutes an attempted local odd-cycle obstruction, not the posted theorem.
It deliberately makes no least-circuit claim.
"""

import json
from itertools import product


N = 5
EDGES = ((0, 1), (1, 2), (2, 3), (3, 4))
# Inputs a,b,c,d,e have indices 0,1,2,3,4. Gate wires start at 5.
GATES = (
    ("or", 2, 4),
    ("or", 0, 5),
    ("or", 1, 3),
    ("and", 6, 7),
    ("or", 1, 5),
    ("and", 8, 9),
    ("or", 0, 2),
    ("or", 11, 3),
    ("and", 10, 12),
)
SHORTER = (
    ("or", 0, 2),
    ("or", 2, 4),
    ("and", 1, 5),
    ("and", 3, 6),
    ("or", 7, 8),
)


def evaluate(gates, bits):
    wires = list(bits)
    for index, (operation, left, right) in enumerate(gates):
        assert left < N + index and right < N + index
        wires.append(wires[left] and wires[right] if operation == "and"
                     else wires[left] or wires[right])
    return wires


def target(bits):
    return any(bits[u] and bits[v] for u, v in EDGES)


def cone(gates, wire):
    if wire < N:
        return set()
    _, left, right = gates[wire - N]
    return {wire} | cone(gates, left) | cone(gates, right)


rows = [(bits, evaluate(GATES, bits)) for bits in product((False, True), repeat=N)]
assert all(wires[-1] == target(bits) for bits, wires in rows)
assert all(evaluate(SHORTER, bits)[-1] == target(bits) for bits, _ in rows)
below = {wire for wire in range(N + len(GATES))
         if all(not wires[wire] or target(bits) for bits, wires in rows)}
and_wires = {N + i for i, gate in enumerate(GATES) if gate[0] == "and"}
junk = and_wires - below
tops = and_wires & below
assert junk == {8, 10}
assert tops == {13}
assert cone(GATES, 13) == set(range(N, N + len(GATES)))
assert all(top not in cone(GATES, other) - {other}
           for top in tops for other in and_wires)
assert all(left not in below and right not in below for operation, left, right in GATES
           if operation == "and")
assert all(not (operation == "or" and N + i not in below and
                (left in below or right in below))
           for i, (operation, left, right) in enumerate(GATES))
accepted = {}
for wire in sorted(junk):
    accepted[wire] = []
    for u, v in EDGES:
        bits = tuple(i in (u, v) for i in range(N))
        if evaluate(GATES, bits)[wire]:
            accepted[wire].append([u, v])
    assert len(accepted[wire]) == 4

# Dynamic enumeration of all proof-tree leaf multiplicity vectors.
vectors = [{tuple(int(i == j) for i in range(N))} for j in range(N)]
for operation, left, right in GATES:
    if operation == "or":
        vectors.append(vectors[left] | vectors[right])
    else:
        vectors.append({tuple(a + b for a, b in zip(v, w))
                        for v in vectors[left] for w in vectors[right]})
for u, v in EDGES:
    assert not any(all(count <= int(i in (u, v)) for i, count in enumerate(vec))
                   for vec in vectors[-1])
    assert any(all(count <= 2 * int(i in (u, v)) for i, count in enumerate(vec))
               for vec in vectors[-1])

print(json.dumps({
    "scope": "Counterexample to a local odd-cycle obstruction; not a least circuit",
    "graph": "path a-b-c-d-e, bipartite and acyclic",
    "assignments_checked": len(rows),
    "circuit_size": len(GATES),
    "strictly_shorter_equivalent_size": len(SHORTER),
    "junk_gate_wires": sorted(junk),
    "accepted_edges_at_each_junk": accepted,
    "top_gate_wires": sorted(tops),
    "top_form": True,
    "lift_fixed_point": True,
    "all_gates_live": True,
    "no_AND_operand_below_target": True,
    "each_edge_requires_read_more_than_one_at_top": True,
    "read_two_suffices_for_each_edge_at_top": True,
}, indent=2))
