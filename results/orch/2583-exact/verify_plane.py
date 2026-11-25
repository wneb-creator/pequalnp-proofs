"""Independent finite premises needed by the checked read-1 lower bound."""
import itertools
import json
from pathlib import Path

source = Path(__file__).resolve().parent.parent / "2583-search" / "plane3.json"
p = json.loads(source.read_text())
edges = set(map(tuple, p["edges"]))
assert len(edges) == 52
neighbors = [{v - 13 for u, v in edges if u == point} for point in range(13)]
assert all(len(ns) == 4 for ns in neighbors)
assert all(len(neighbors[a] & neighbors[b]) == 1
           for a, b in itertools.combinations(range(13), 2))

owner = {}


def augment(point, seen):
    for line in sorted(neighbors[point]):
        if line in seen:
            continue
        seen.add(line)
        if line not in owner or augment(owner[line], seen):
            owner[line] = point
            return True
    return False


assert all(augment(point, set()) for point in range(13))
permutation = [next(line for line, point in owner.items() if point == pnt)
               for pnt in range(13)]
assert sorted(permutation) == list(range(13))
assert all((point, 13 + line) in edges for point, line in enumerate(permutation))
print(json.dumps(dict(edges=52, squarefree=True, matching=permutation,
                      read1_lower_bound=52 + 13 - 1), sort_keys=True))
