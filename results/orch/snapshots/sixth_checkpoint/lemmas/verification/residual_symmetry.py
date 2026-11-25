#!/usr/bin/env python3
"""Enumerate incidence-preserving permutations fixing the removed point zero."""

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path


def generate(statement):
    expected = "2f423a13954b274d19d1c8766b82e12bb5ea843a124eebfdc6e995defee5b630"
    if hashlib.sha256(statement.strip().encode()).hexdigest() != expected:
        raise ValueError("statement does not match the assigned target")
    edges = {(int(a), int(b) - 13) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", statement)}
    assert len(edges) == 52
    point_lines = [{l for p, l in edges if p == i} for i in range(13)]
    line_points = [{p for p, l in edges if l == i} for i in range(13)]

    def join(a, b):
        values = point_lines[a] & point_lines[b]
        assert a != b and len(values) == 1
        return next(iter(values))

    def meet(a, b):
        values = line_points[a] & line_points[b]
        assert a != b and len(values) == 1
        return next(iter(values))

    base = (0, 1, 2, 6)
    assert all(c not in line_points[join(a, b)] for a, b, c in itertools.combinations(base, 3))
    permutations = []
    for a in range(1, 13):
        for b in range(1, 13):
            if b in line_points[join(0, a)]:
                continue
            forbidden = line_points[join(0, a)] | line_points[join(0, b)] | line_points[join(a, b)]
            for c in set(range(13)) - forbidden:
                points = dict(zip(base, (0, a, b, c)))
                lines = {}

                def insert(mapping, key, value):
                    if key in mapping:
                        assert mapping[key] == value
                    else:
                        assert value not in mapping.values()
                        mapping[key] = value

                while len(points) < 13 or len(lines) < 13:
                    before = len(points) + len(lines)
                    for u, v in itertools.combinations(list(points), 2):
                        insert(lines, join(u, v), join(points[u], points[v]))
                    for u, v in itertools.combinations(list(lines), 2):
                        insert(points, meet(u, v), meet(lines[u], lines[v]))
                    assert len(points) + len(lines) > before
                full = [points[i] for i in range(13)] + [13 + lines[i] for i in range(13)]
                assert full[0] == 0 and sorted(full) == list(range(26))
                assert {(full[p], full[l + 13] - 13) for p, l in edges} == edges
                residual = [full[i + 1] - 1 for i in range(25)]
                permutations.append(residual)
    assert len(permutations) == len({tuple(p) for p in permutations}) == 432
    pairs = set(itertools.combinations(range(25), 2))
    orbits = []
    while pairs:
        representative = min(pairs)
        orbit = {tuple(sorted((p[representative[0]], p[representative[1]]))) for p in permutations}
        assert orbit <= pairs
        pairs -= orbit
        orbits.append({"representative": list(representative), "pairs": [list(p) for p in sorted(orbit)]})
    tap = {l + 12 for l in point_lines[0]}
    assert all({p[i] for i in tap} == tap for p in permutations)
    return {
        "status": "verified combinatorial symmetry data; not a circuit or a lower bound",
        "removed_full_input": 0,
        "residual_input_to_full": list(range(1, 26)),
        "tap_inputs": sorted(tap),
        "permutations": permutations,
        "first_gate_pair_orbits": orbits,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("statement", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = generate(args.statement.read_text())
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"permutations": len(data["permutations"]), "pair_orbit_sizes": [len(o["pairs"]) for o in data["first_gate_pair_orbits"]]}))


if __name__ == "__main__":
    main()
