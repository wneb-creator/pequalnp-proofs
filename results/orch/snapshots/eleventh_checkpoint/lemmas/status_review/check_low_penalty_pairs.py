"""Finite corroboration of the L5869 low-penalty geometric consequence.

This is not a Lean certificate or a full target result. Output goes only to
this script's research directory. No network or external program is used.
"""

import json
from itertools import combinations
from pathlib import Path


def adjacent(a, b):
    return ((a < 13 <= b and (a + b - 13) % 13 in (0, 1, 3, 9))
            or (b < 13 <= a and (a + b - 13) % 13 in (0, 1, 3, 9)))


def main():
    checks = []
    for v in range(26):
        arms = [(w, p) for w in range(26) if adjacent(v, w)
                for p in range(26) if p != v and adjacent(w, p)]
        assert len(arms) == 12
        for e, f in combinations(arms, 2):
            w, p = e
            z, q = f
            assert p != q
            witness = {w} if w == z else {w, q}
            forced = {p, q} if w == z else {p, z}
            assert len(forced) == 2 and forced.isdisjoint(witness)
            assert all(not adjacent(a, b) for a, b in combinations(witness, 2))
            removed = {tuple(sorted(e)), tuple(sorted(f))}

            def remaining_adjacent(a, b):
                return adjacent(a, b) and tuple(sorted((a, b))) not in removed

            def covers(cover):
                return bool(set(e) & cover) and bool(set(f) & cover)

            assert not any(covers({a}) for a in range(26) if a not in witness)
            assert not any(covers({a for a in range(26) if a not in witness
                                   and remaining_adjacent(a, c)}) for c in range(26))
            assert not any(all(remaining_adjacent(a, c) for a in forced)
                           for c in range(26))
            checks.append({"center": v, "edges": [list(e), list(f)],
                           "independent_mask": sum(1 << a for a in witness)})
    assert len(checks) == 1716
    destination = Path(__file__).parent / "reviewer-low-penalty-pair-witnesses.json"
    expected = json.loads(destination.read_text())
    assert checks == expected
    print("PASS all1716 cases; existing frozen witness data reproduced exactly")
    print("No singleton or common-neighbor cover avoids the independent witness")


if __name__ == "__main__":
    main()
