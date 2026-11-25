"""Check the P4 obstruction to an essential-star gate induction.

This is a finite Python check, not a Lean theorem. No solver is invoked.
Free-OR normalization explains completeness of the one-AND enumeration.
"""

import itertools
import json


EDGES = [(0, 1), (1, 2), (2, 3)]


def target(mask):
    return any(mask & (1 << a) and mask & (1 << b) for a, b in EDGES)


def circuit(mask, forced=None):
    a, b, c, d = (bool(mask & (1 << i)) for i in range(4))
    g = False if forced == 0 else (a or c) and (b or d)
    h = False if forced == 1 else g and (b or c)
    return h


def main():
    truth = []
    for mask in range(16):
        expected = target(mask)
        observed = circuit(mask)
        assert observed == expected, (mask, observed, expected)
        truth.append([mask, int(expected), int(observed)])
    essential = []
    for gate in range(2):
        lost = [edge for edge in EDGES if not circuit(sum(1 << v for v in edge), gate)]
        assert lost == EDGES
        assert not any(all(v in edge for edge in lost) for v in range(4))
        essential.append(lost)
    edge_set = {frozenset(edge) for edge in EDGES}
    for a, b, c in itertools.permutations(range(4), 3):
        assert not all(frozenset(e) in edge_set for e in [(a, b), (b, c), (c, a)])
    for a, b, c, d in itertools.permutations(range(4), 4):
        assert not all(frozenset(e) in edge_set for e in [(a, b), (b, c), (c, d), (d, a)])
    # With at most one AND and free ORs, a singleton-silent nonzero output
    # is one conjunction of two ORs of primary variables. True constants
    # reduce to an OR/alias, rejected by singleton silence. A primary term
    # cannot be included directly at the output for the same reason.
    one_and_solutions = []
    for left in range(16):
        for right in range(16):
            if all((bool(mask & left) and bool(mask & right)) == target(mask)
                   for mask in range(16)):
                one_and_solutions.append([left, right])
    assert one_and_solutions == []
    print(json.dumps({
        "graph": "P4",
        "edges": EDGES,
        "circuit": ["g=(a OR c) AND (b OR d)", "h=g AND (b OR c)"],
        "truth_table_mask_expected_observed": truth,
        "essential_edges_per_and": essential,
        "triangle_free": True,
        "four_cycle_free": True,
        "one_and_source_pairs_exhausted": 256,
        "one_and_solutions": one_and_solutions,
        "minimum_and_count": 2,
        "witness_total_binary_gates": 5,
        "canonical_total_binary_gates": 4,
        "conclusion": "No AND has a star essential-edge set, despite minimum AND count.",
        "limitation": "Python finite verification plus reviewed free-OR normalization, not Lean."
    }, indent=2))


if __name__ == "__main__":
    main()
