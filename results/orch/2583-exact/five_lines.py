"""Classify all five-line sub-incidence functions up to line permutation."""
import itertools
import json
from pathlib import Path

directory = Path(__file__).resolve().parent
plane = json.loads((directory.parent / "2583-search" / "plane3.json").read_text())
relabelings = [[sum(((mask >> i) & 1) << perm[i] for i in range(5))
               for mask in range(32)] for perm in itertools.permutations(range(5))]
classes = {}
for chosen in itertools.combinations(range(13), 5):
    patterns = [sum((point in plane["lines"][ell]) << i
                    for i, ell in enumerate(chosen)) for point in range(13)]
    patterns = [mask for mask in patterns if mask]
    canonical = min(tuple(sorted(relabel[mask] for mask in patterns))
                    for relabel in relabelings)
    if canonical not in classes:
        classes[canonical] = dict(chosen=chosen, copies=0)
    classes[canonical]["copies"] += 1

summaries = []
for number, (canonical, record) in enumerate(sorted(classes.items()), 1):
    chosen = record["chosen"]
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
    assert len(gates) == 24 and len(edges) == 20
    graph = dict(inputs=n, bipartition=([i for i in range(n - 5)], [i for i in range(n - 5, n)]),
                 edges=edges, local_to_plane=mapping, selected_lines=chosen,
                 gates=gates, output=wire)
    (directory / f"lines5-type{number}.json").write_text(json.dumps(graph, indent=2) + "\n")
    groups = {}
    for point in original_points:
        pattern = sum((point in plane["lines"][ell]) << i for i, ell in enumerate(chosen))
        groups.setdefault(pattern, []).append(point)
    grouped = sorted(groups.items())
    extra = sum(len(points) - 1 for pattern, points in grouped)
    assert all(len(points) == 1 or pattern.bit_count() == 1 for pattern, points in grouped)
    cn = len(grouped) + 5
    compressed_edges = [(j, len(grouped) + k) for j, (pattern, points) in enumerate(grouped)
                        for k in range(5) if (pattern >> k) & 1]
    compressed = dict(inputs=cn, bipartition=(list(range(len(grouped))), list(range(len(grouped), cn))),
                      edges=compressed_edges, selected_lines=chosen,
                      point_input_groups=[points for pattern, points in grouped],
                      outside_or_gates=extra, target_gates=23 - extra)
    (directory / f"lines5-type{number}-compressed.json").write_text(json.dumps(compressed, indent=2) + "\n")
    summary = dict(type=number, copies=record["copies"], selected_lines=chosen,
                   inputs=n, point_degrees={str(k): sum(mask.bit_count() == k for mask in canonical)
                                            for k in range(1, 5)},
                   canonical_patterns=canonical, compressed_inputs=cn,
                   compressed_target=23-extra, outside_or_gates=extra)
    summaries.append(summary)
    print(json.dumps(summary), flush=True)
assert sum(x["copies"] for x in summaries) == 1287
(directory / "five-line-classes.json").write_text(json.dumps(summaries, indent=2) + "\n")
