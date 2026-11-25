#!/usr/bin/env python3
"""Check the explicit Fano incidence action of GL(3, 2)."""

import itertools
import json
from pathlib import Path
import sys


def dot(v, w):
    return (v & w).bit_count() % 2


def apply(rows, v):
    return sum(dot(row, v) << i for i, row in enumerate(rows))


def transpose(rows):
    return tuple(sum(((rows[j] >> i) & 1) << j for j in range(3)) for i in range(3))


def main():
    data = json.loads(Path(sys.argv[1]).read_text())
    edges = {tuple(e) for e in data["edges"]}
    expected = {(p, 7 + l) for p in range(7) for l in range(7) if dot(p + 1, l + 1) == 0}
    assert edges == expected and len(edges) == 21
    base = (0, 8)
    assert base in edges
    group = []
    representatives = {}
    for rows in itertools.product(range(8), repeat=3):
        values = [apply(rows, v) for v in range(8)]
        if len(set(values)) != 8:
            continue
        inverse_values = {w: v for v, w in enumerate(values)}
        inverse_rows = tuple(
            sum(((inverse_values[1 << j] >> i) & 1) << j for j in range(3))
            for i in range(3)
        )
        dual_rows = transpose(inverse_rows)
        for v in range(8):
            assert apply(inverse_rows, apply(rows, v)) == v
            assert apply(rows, apply(inverse_rows, v)) == v
            for l in range(8):
                assert dot(apply(rows, v), apply(dual_rows, l)) == dot(v, l)
        points = [apply(rows, p + 1) - 1 for p in range(7)]
        lines = [apply(dual_rows, l + 1) - 1 for l in range(7)]
        assert sorted(points) == list(range(7))
        assert sorted(lines) == list(range(7))
        image = {(points[p], 7 + lines[l - 7]) for p, l in edges}
        assert image == edges
        target = (points[base[0]], 7 + lines[base[1] - 7])
        record = {
            "point_matrix_rows": list(rows),
            "line_matrix_rows": list(dual_rows),
            "point_permutation": points,
            "line_permutation": lines,
            "base_image": list(target),
        }
        group.append(record)
        representatives.setdefault(target, record)
    assert len(group) == 168
    assert set(representatives) == edges
    stabilizer = sum(tuple(g["base_image"]) == base for g in group)
    assert stabilizer == 8
    report = {
        "incidence": "parity((p+1)&(l+1))=0 for p,l in 0..6",
        "matrix_encoding": "three integer row bitmasks; coordinate bit 0 is least significant",
        "action": "point vector v maps to A v; line vector l maps to inverse(A)^T l",
        "base_edge_global_wires": list(base),
        "group_order": len(group),
        "edge_count": len(edges),
        "edge_orbit_size": len(representatives),
        "edge_stabilizer_order": stabilizer,
        "all_21_edge_representatives": [representatives[e] for e in sorted(edges)],
        "all_168_actions": group,
        "checks": "all 64 dot products, both inverse identities, both permutations, and all21 edges for each action",
    }
    Path(sys.argv[2]).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["base_edge_global_wires", "group_order", "edge_count", "edge_orbit_size", "edge_stabilizer_order", "checks"]}))


if __name__ == "__main__":
    main()
