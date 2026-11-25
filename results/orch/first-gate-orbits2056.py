"""Enumerate input-pair orbits of the Singer-13 sum-incidence plane.

This is a finite search aid, not a Lean certificate or circuit lower bound.
The four first-gate cases additionally require the minimum-circuit arguments
that delete a copy gate or a gate with zero minimal-true-row profile.
"""

import argparse
import json
from itertools import product
from pathlib import Path


def normalize(vector):
    first = next(value for value in vector if value)
    inverse = 1 if first == 1 else 2
    return tuple(value * inverse % 3 for value in vector)


def determinant(matrix):
    a = matrix
    return (a[0] * (a[4] * a[8] - a[5] * a[7])
            - a[1] * (a[3] * a[8] - a[5] * a[6])
            + a[2] * (a[3] * a[7] - a[4] * a[6])) % 3


def census():
    difference_set = {0, 1, 3, 9}
    points = []
    vector = (1, 0, 0)
    for _ in range(13):
        points.append(normalize(vector))
        vector = (vector[2], (vector[0] + vector[2]) % 3, vector[1])
    point_index = {point: i for i, point in enumerate(points)}
    assert len(point_index) == 13
    lines = [frozenset((line + d) % 13 for d in difference_set)
             for line in range(13)]
    line_index = {line: i for i, line in enumerate(lines)}
    edges = {(point, 13 + line) for point in range(13)
             for line in range(13) if (point + line) % 13 in difference_set}
    representatives = [(0, 1), (0, 13), (0, 15)]
    orbits = [set() for _ in representatives]
    matrix_count = 0
    for matrix in product(range(3), repeat=9):
        if next((value for value in matrix if value), 0) != 1:
            continue
        if not determinant(matrix):
            continue
        point_permutation = tuple(point_index[normalize(tuple(
            sum(matrix[3 * row + col] * point[col] for col in range(3)) % 3
            for row in range(3)))] for point in points)
        line_permutation = tuple(line_index[frozenset(
            point_permutation[point] for point in line)] for line in lines)
        # Difference incidence uses p-l in D. Negating line labels gives p+l.
        permutation = point_permutation + tuple(
            13 + (-line_permutation[(-line) % 13]) % 13 for line in range(13))
        assert len(set(permutation)) == 26
        assert {(permutation[p], permutation[l]) for p, l in edges} == edges
        for orbit, (left, right) in zip(orbits, representatives):
            pair = tuple(sorted((permutation[left], permutation[right])))
            orbit.add(pair)
            # Sum incidence is symmetric, so swapping the two sides is duality.
            orbit.add(tuple(sorted(((pair[0] + 13) % 26,
                                    (pair[1] + 13) % 26))))
        matrix_count += 1
    all_pairs = {(left, right) for left in range(26)
                 for right in range(left + 1, 26)}
    assert matrix_count == 5616
    assert set.union(*orbits) == all_pairs
    assert sum(map(len, orbits)) == 325
    assert list(map(len, orbits)) == [156, 52, 117]
    return {
        "sum_incidence_D": sorted(difference_set),
        "collineations_checked": matrix_count,
        "automorphisms_with_duality": 2 * matrix_count,
        "unordered_pair_orbits": [
            {"representative": list(rep), "size": len(orbit),
             "members": [list(pair) for pair in sorted(orbit)]}
            for rep, orbit in zip(representatives, orbits)],
        "first_gate_representatives": [[1, 0, 1], [1, 0, 13],
                                       [1, 0, 15], [0, 0, 13]],
        "scope": "Finite orbit census. First-gate normal form additionally uses "
                 "deletion of copies and positive-zero gates in a size-minimum circuit.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = census()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"collineations": result["collineations_checked"],
                      "orbit_sizes": [row["size"] for row in result["unordered_pair_orbits"]]}))
