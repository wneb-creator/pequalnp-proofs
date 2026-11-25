"""Check a local OR-sharing obstruction, not a minimum graph circuit.

The four outputs are explicitly required in a multioutput OR subproblem.
Their distinct-output lower bound does not transfer to a single graph output.
"""

from itertools import combinations
import json


def inputs(n):
    return [sum(1 << x for x in range(1 << n) if x & (1 << v))
            for v in range(n)]


# The four-output OR network: a,d,b,f are independent Boolean inputs.
v = inputs(4)
a, b, d, f = v
required = [a | d, b | f, a | b | d, a | b | f]
constructed = [a | d, b | f]
constructed += [constructed[0] | b, constructed[1] | a]
assert constructed == required
assert len(set(required)) == 4
assert not set(required) & set(v)
assert a | b not in v + required
print(json.dumps({"four_output_or_problem": {
    "required": ["a OR d", "b OR f", "a OR b OR d", "a OR b OR f"],
    "constructed_gates": 4,
    "lower_bound_by_distinct_noninput_outputs": 4,
    "common_or_a_b_absent": True,
    "scope": "explicit multioutput OR subproblem, not full graph minimum"}}))


# A compatible graph on z,a,b,c,d,e,f,r,s: C7 plus an isolated edge.
n = 9
v = inputs(n)
z, a, b, c, d, e, f, r, s = v
edges = [(0, 1), (0, 2), (3, 5), (4, 6), (1, 7), (4, 7), (2, 8), (6, 8)]
neighbors = [set() for _ in range(n)]
for u, w in edges:
    neighbors[u].add(w)
    neighbors[w].add(u)
assert all(not neighbors[u] & neighbors[w] for u, w in edges)
assert all(len(neighbors[u] & neighbors[w]) <= 1 for u, w in combinations(range(n), 2))
cycle = [0, 1, 7, 4, 6, 8, 2]
cycle_edges = {tuple(sorted((cycle[i], cycle[(i + 1) % 7]))) for i in range(7)}
assert set(edges) == cycle_edges | {(3, 5)}
target = 0
for u, w in edges:
    target |= v[u] & v[w]
t1, t2 = a | d, b | f
p = (z | c) & (t1 | b)
q = (z | e) & (t2 | a)
j = p & q
assert j | target == target
assert not (p >> 1) & 1 and not (q >> 1) & 1  # Singleton z.
accepted = [edge for edge in edges if (j >> sum(1 << u for u in edge)) & 1]
assert accepted == [(0, 1), (0, 2)]
assert all((p >> sum(1 << u for u in edge)) & 1 for edge in accepted)
assert all((q >> sum(1 << u for u in edge)) & 1 for edge in accepted)
# Earlier p/q are ANDs whose ancestors are only ORs, so they own those edges;
# the top j has both as true AND ancestors and owns none.
assert (z & q) >> ((1 << 0) | (1 << 6)) & 1  # Spurious z-f.
assert (z & p) >> ((1 << 0) | (1 << 4)) & 1  # Spurious z-d.
assert not (target >> ((1 << 0) | (1 << 6))) & 1
assert not (target >> ((1 << 0) | (1 << 4))) & 1
complete_output = j | (c & e) | (d & f) | (r & t1) | (s & t2)
assert complete_output == target
smaller_output = (z & a) | (b & (z | s)) | (c & e) | (f & (d | s)) | (r & (a | d))
assert smaller_output == target
print(json.dumps({"graph_compatibility": {
    "n": n, "edges": edges, "cycle": cycle, "isolated_edge": [3, 5],
    "triangle_free": True, "no_four_cycle": True,
    "j_safe": True, "j_accepted_graph_edges": accepted,
    "both_operands_reject_singleton_center": True,
    "j_owns_no_graph_edge": True,
    "complete_nonminimum_circuit_correct_on_all_inputs": True,
    "displayed_full_circuit_gates": 17,
    "verified_smaller_full_circuit_gates": 12,
    "scope": "compatible local sharing in a nonminimum graph circuit"}}))


for k in range(2, 5):
    n = k + 2
    v = inputs(n)
    raw_a = v[:k]
    d, f = v[k:]
    prefixes = []
    left, right = d, f
    for i in range(k):
        left |= raw_a[i]
        right |= raw_a[k - i - 1]
        prefixes += [left, right]
    target = 0
    for a in raw_a:
        target |= a
    assert len(set(prefixes)) == 2 * k
    assert not set(prefixes) & set(v)
    assert target not in v + prefixes
    reference = (1 << k) | (1 << (k + 1))
    assert all((p >> reference) & 1 for p in prefixes)
    base = tuple(sorted(set(v + prefixes + [0, (1 << (1 << n)) - 1])))
    states = {()}
    found = target in base
    counts = []
    # Exhaustive small confirmation: no fewer than k-1 new monotone gates.
    for depth in range(1, k - 1):
        new = set()
        for state in states:
            vals = base + state
            available = set(vals)
            for a, b in combinations(vals, 2):
                for value in (a & b, a | b):
                    if value in available:
                        continue
                    found |= value == target
                    new.add(tuple(sorted(state + (value,))))
        states = new
        counts.append({"depth": depth, "states": len(states)})
    assert not found
    print(json.dumps({"polluted_prefix_problem": {
        "k": k, "required_prefix_outputs": 2 * k,
        "minimum_or_gates_for_required_outputs": 2 * k,
        "tested_extraction_new_gate_bound": k - 2,
        "extraction_found": found, "state_counts": counts,
        "extraction_witness_gates": k - 1,
        "scope": "clean OR of leaves from free polluted prefixes"}}))
