"""Build directly spliceable subfunctions on three/four general-position lines."""
import itertools
import json
from pathlib import Path

directory = Path(__file__).resolve().parent
plane = json.loads((directory.parent / "2583-search" / "plane3.json").read_text())
for count in (3, 4):
    chosen = next(ls for ls in itertools.combinations(range(13), count)
                  if max(sum(p in plane["lines"][ell] for ell in ls)
                         for p in range(13)) <= 2)
    original_points = sorted(set().union(*(set(plane["lines"][ell]) for ell in chosen)))
    mapping = original_points + [13 + ell for ell in chosen]
    inverse = {v: i for i, v in enumerate(mapping)}
    edges = [(inverse[p], inverse[13 + ell])
             for ell in chosen for p in plane["lines"][ell]]
    n = len(mapping)
    gates, stars = [], []
    for ell in chosen:
        vertices = [inverse[p] for p in plane["lines"][ell]]
        wire = vertices[0]
        for vertex in vertices[1:]:
            gates.append(dict(op="or", a=wire, b=vertex))
            wire = n + len(gates) - 1
        gates.append(dict(op="and", a=wire, b=inverse[13 + ell]))
        stars.append(n + len(gates) - 1)
    wire = stars[0]
    for star in stars[1:]:
        gates.append(dict(op="or", a=wire, b=star))
        wire = n + len(gates) - 1
    graph = dict(inputs=n, edges=edges, local_to_plane=mapping,
                 selected_lines=chosen, gates=gates, output=wire)
    (directory / f"lines{count}.json").write_text(json.dumps(graph, indent=2) + "\n")
    print(json.dumps(dict(lines=chosen, inputs=n, edges=len(edges), gates=len(gates))))
