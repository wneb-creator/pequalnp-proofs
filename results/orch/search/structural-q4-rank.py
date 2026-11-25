import itertools
import json
from pathlib import Path

data = json.loads(Path("/tmp/oec/pequalnp-pilot-76/structural-q4-baer.json").read_text())
partial = data["outside_block_permutation_bits"]
constraints = [(sum(1 << j for j, x in enumerate(row) if x is not None),
                sum(x << j for j, x in enumerate(row) if x is not None)) for row in partial]


def subspaces(n, r):
    for pivots in itertools.combinations(range(n), r):
        places = [(i, j) for i, p in enumerate(pivots) for j in range(p + 1, n) if j not in pivots]
        for code in range(1 << len(places)):
            basis = [1 << p for p in pivots]
            for k, (i, j) in enumerate(places):
                if code >> k & 1:
                    basis[i] |= 1 << j
            space = [0]
            for b in basis:
                space += [v ^ b for v in space]
            yield basis, space


result = None
tested = []
for rank in range(5):
    count = 0
    for basis, space in subspaces(7, rank):
        count += 1
        choices = [next((v for v in space if v & mask == value), None) for mask, value in constraints]
        if all(v is not None for v in choices):
            result = {"minimum_rank": rank, "basis": basis, "row_vectors": choices,
                      "completed_matrix": [[v >> j & 1 for j in range(7)] for v in choices]}
            break
    tested.append({"rank": rank, "subspaces_tested": count})
    if result is not None:
        break
result = {"tested": tested, "completion": result}
Path("/tmp/oec/pequalnp-pilot-76/structural-q4-rank.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
