"""Exact finite diagnostics for the six-literal first-bad-AND motif.

This is computational evidence, not a Lean certificate.  It does not refute
existence of a minimum circuit with ownership.  Free sources are the six
variables, both constants, and the four original OR2 outputs.  Breadth-first
search permits either binary monotone operation and arbitrary source reuse.
States retain the set of newly available truth tables.  This loses no minimum
size solution: duplicate truth tables can always be redirected to an earlier
wire, and future operations depend only on available truth tables.
"""

from itertools import combinations
import json
import time


N = 6
ALL = (1 << (1 << N)) - 1
INPUTS = tuple(sum(1 << x for x in range(1 << N) if x & (1 << i))
               for i in range(N))
# z=0, p=1, q=2, r=3, a=4, b=5.
FACTORS = ((0, 1), (0, 2), (0, 3), (4, 5))
MANDATORY = {(0, 4), (0, 5), (1, 2)}
TARGET_EDGES = sorted(MANDATORY | {(3, 4)})
BASE = tuple(sorted(set((0, ALL) + INPUTS +
                        tuple(INPUTS[a] | INPUTS[b] for a, b in FACTORS))))
TARGET = 0
for a, b in TARGET_EDGES:
    TARGET |= INPUTS[a] & INPUTS[b]


def girth_at_least_five(edges):
    nbr = [set() for _ in range(N)]
    for a, b in edges:
        nbr[a].add(b)
        nbr[b].add(a)
    if any(nbr[a] & nbr[b] for a, b in edges):
        return False
    return all(len(nbr[a] & nbr[b]) <= 1 for a, b in combinations(range(N), 2))


optional = sorted(set(combinations(range(N), 2)) - MANDATORY)
extensions = []
signature_counts = {}
for mask in range(1 << len(optional)):
    edges = MANDATORY | {edge for i, edge in enumerate(optional) if mask & (1 << i)}
    if not girth_at_least_five(edges):
        continue
    extensions.append(edges)
    # The extra graph pairs accepted by the second rectangle.
    signature = tuple(edge for edge in ((3, 4), (3, 5)) if edge in edges)
    signature_counts[signature] = signature_counts.get(signature, 0) + 1
assert girth_at_least_five(set(TARGET_EDGES))
print(json.dumps({"phase": "graph_extensions", "mandatory_edges": sorted(MANDATORY),
                  "total_extensions": len(extensions),
                  "right_extra_signatures": [
                      {"edges": sig, "count": count}
                      for sig, count in sorted(signature_counts.items())],
                  "local_target_edges": TARGET_EDGES}), flush=True)


def last_gate(values):
    # Exhaustive final-gate test, filtered by necessary containment conditions.
    below = [v for v in values if v | TARGET == TARGET]
    for a, b in combinations(below, 2):
        if a | b == TARGET:
            return ("or", a, b)
    above = [v for v in values if v & TARGET == TARGET]
    for a, b in combinations(above, 2):
        if a & b == TARGET:
            return ("and", a, b)
    return None


start = time.monotonic()
states = {()}
found_depth = None
for depth in range(1, 5):
    if depth == 4:
        found = next((state for state in states if last_gate(BASE + state)), None)
        print(json.dumps({"phase": "final_gate_scan", "depth": depth,
                          "prefix_states": len(states), "found": found is not None,
                          "seconds": time.monotonic() - start}), flush=True)
        if found is not None:
            found_depth = depth
        break
    new = set()
    for state in states:
        values = BASE + state
        available = set(values)
        for a, b in combinations(values, 2):
            for value in (a & b, a | b):
                if value in available:
                    continue
                if value == TARGET:
                    found_depth = depth
                new.add(tuple(sorted(state + (value,))))
    states = new
    print(json.dumps({"phase": "bfs", "depth": depth, "states": len(states),
                      "found": found_depth is not None,
                      "seconds": time.monotonic() - start}), flush=True)
    if found_depth is not None:
        break

# Explicit five-operation construction from free source z OR r.
pq = INPUTS[1] & INPUTS[2]
arza = INPUTS[4] & (INPUTS[0] | INPUTS[3])
zb = INPUTS[0] & INPUTS[5]
combined = pq | arza
output = combined | zb
assert output == TARGET
print(json.dumps({"phase": "result", "found_depth_through_four": found_depth,
                  "five_gate_witness_verified_on_all_assignments": True,
                  "witness": ["p AND q", "a AND (z OR r)", "z AND b",
                              "gate0 OR gate1", "gate3 OR gate2"],
                  "minimum_new_gates": 5 if found_depth is None else found_depth,
                  "scope": "single safe repair signal over twelve free source tables",
                  "seconds": time.monotonic() - start}), flush=True)
