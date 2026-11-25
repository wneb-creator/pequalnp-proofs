"""Exact graph automorphisms and pair orbits, including bipartition swaps."""
import itertools
import json
from pathlib import Path

here = Path(__file__).resolve().parent
data = json.loads((here / "data.json").read_text())
edges = {tuple(sorted(e)) for e in data["edges"]}
adj = [{b if a == v else a for a, b in edges if a == v or b == v}
       for v in range(14)]
assert len(edges) == 19
assert all((a < 7) != (b < 7) for a, b in edges)
seen = {0}
while True:
    extended = seen | set().union(*(adj[v] for v in seen))
    if extended == seen:
        break
    seen = extended
assert len(seen) == 14

automorphisms = []
for swap in (False, True):
    image_left = range(7, 14) if swap else range(7)
    image_right = range(7) if swap else range(7, 14)
    by_neighbors = {frozenset(adj[v]): v for v in image_right}
    assert len(by_neighbors) == 7
    for p in itertools.permutations(image_left):
        q = list(p)
        for v in range(7, 14):
            key = frozenset(p[u] for u in adj[v])
            if key not in by_neighbors:
                break
            q.append(by_neighbors[key])
        else:
            assert sorted(q) == list(range(14))
            assert {tuple(sorted((q[a], q[b]))) for a, b in edges} == edges
            automorphisms.append(q)
group = {tuple(q) for q in automorphisms}
assert tuple(range(14)) in group
assert all(tuple(q[p[v]] for v in range(14)) in group
           for p in automorphisms for q in automorphisms)

pending = set(itertools.combinations(range(14), 2))
orbits = []
while pending:
    rep = min(pending)
    orbit = {tuple(sorted((p[rep[0]], p[rep[1]]))) for p in automorphisms}
    assert orbit <= pending
    pending -= orbit
    kind = "edge" if rep in edges else "same_side" if (rep[0] < 7) == (rep[1] < 7) else "cross_nonedge"
    assert all((pair in edges) == (kind == "edge") for pair in orbit)
    orbits.append({"representative": rep, "kind": kind,
                   "size": len(orbit), "pairs": sorted(orbit)})
result = {"group_order": len(automorphisms),
          "side_preserving": sum(p[0] < 7 for p in automorphisms),
          "side_swapping": sum(p[0] >= 7 for p in automorphisms),
          "complete_by": "connected bipartite graph; all 7! permutations of one side, for each bipartition orientation; distinct neighborhoods force the other side",
          "automorphisms": automorphisms, "pair_orbits": orbits,
          "all_pairs_checked": sum(o["size"] for o in orbits),
          "group_closure_checked": True}
(here / "automorphisms.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k not in {"automorphisms", "pair_orbits"}}, indent=2))
for orbit in orbits:
    print(orbit["kind"], orbit["representative"], orbit["size"])
