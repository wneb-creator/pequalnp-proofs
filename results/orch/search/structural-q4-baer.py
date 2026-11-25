import itertools
import json
from pathlib import Path


def mul(a, b):
    result = 0
    for _ in range(2):
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7
    return result


def dot(p, l):
    return mul(p[0], l[0]) ^ mul(p[1], l[1]) ^ mul(p[2], l[2])


vertices = [v for v in itertools.product(range(4), repeat=3)
            if any(v) and next(x for x in v if x) == 1]
n = len(vertices)
assert n == 21
inc = [[dot(p, l) == 0 for l in vertices] for p in vertices]
assert all(sum(row) == 5 for row in inc)
assert all(sum(inc[p][l] and inc[r][l] for l in range(n)) == 1
           for p in range(n) for r in range(p + 1, n))
base = [i for i, v in enumerate(vertices) if all(x in (0, 1) for x in v)]
outside = [i for i in range(n) if i not in base]
assert len(base) == 7 and len(outside) == 14
point_groups = {l: [p for p in outside if inc[p][l]] for l in base}
line_groups = {p: [l for l in outside if inc[p][l]] for p in base}
assert all(len(g) == 2 for g in point_groups.values())
assert all(len(g) == 2 for g in line_groups.values())
assert all(sum(p in g for g in point_groups.values()) == 1 for p in outside)
assert all(sum(l in g for g in line_groups.values()) == 1 for l in outside)
blocks = []
for base_l, ps in point_groups.items():
    row = []
    for base_p, ls in line_groups.items():
        matrix = [[int(inc[p][l]) for l in ls] for p in ps]
        if inc[base_p][base_l]:
            assert matrix == [[0, 0], [0, 0]]
            row.append(None)
        else:
            assert matrix in ([[1, 0], [0, 1]], [[0, 1], [1, 0]])
            row.append(matrix[0][1])
    blocks.append(row)
counts = {
    "base_base": sum(inc[p][l] for p in base for l in base),
    "base_outside": sum(inc[p][l] for p in base for l in outside),
    "outside_base": sum(inc[p][l] for p in outside for l in base),
    "outside_outside": sum(inc[p][l] for p in outside for l in outside),
}
result = {
    "q": 4, "N": n, "edges": sum(map(sum, inc)), "canonical_size": n * 6 - 1,
    "coordinates": vertices, "baer_subplane_indices": base,
    "partition_edge_counts": counts,
    "outside_point_groups_by_base_line": point_groups,
    "outside_line_groups_by_base_point": line_groups,
    "outside_block_permutation_bits": blocks,
    "outside_canonical_size": counts["outside_outside"] + len(outside) - 1,
}
Path("/tmp/oec/pequalnp-pilot-76/structural-q4-baer.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ("q", "N", "edges", "canonical_size",
      "partition_edge_counts", "outside_canonical_size", "outside_block_permutation_bits")}, indent=2))
