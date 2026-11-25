"""Replay the stored 20-gate witness profile; performs no synthesis."""
import argparse
import itertools
import json
from pathlib import Path
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("witness", type=Path)
args = parser.parse_args()
w = json.loads(args.witness.read_text())
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
report = []
for p, line in edges:
    vectors = [{(int(i == p), int(i == line))} if i in (p, line) else set()
               for i in range(10)]
    for gate in w["gates"]:
        a, b = gate["inputs"]
        vectors.append(vectors[a] | vectors[b] if gate["op"] == "or" else
                       {(min(x+u,2), min(y+v,2))
                        for x,y in vectors[a] for u,v in vectors[b]})
    if (1,1) not in vectors[w["output"]]:
        report.append({"edge": [p,line], "vectors": sorted(vectors[w["output"]])})
minimum_edges = {}
for k in range(4,8):
    masks = [sum(1 << i for i in subset) for subset in itertools.combinations(range(10),k)]
    minimum_edges[k] = min(sum(bool(mask & (1 << u)) and bool(mask & (1 << v))
                              for u,v in edges) for mask in masks)
print(json.dumps({"nonread_edges": report,
                  "minimum_edges_in_k_vertices": minimum_edges}, indent=2))
