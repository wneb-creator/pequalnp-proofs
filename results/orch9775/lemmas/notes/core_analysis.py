"""Exact small combinatorial checks for the partially subdivided Fano core."""
import itertools
import json
from pathlib import Path

NEIGHBORS = {0:[8,10],1:[7,9,13],2:[8,13],3:[7,11,12],
             4:[10,11,13],5:[9,10,12],6:[8,9,11]}
EDGES = {tuple(sorted((a,b))) for a,bs in NEIGHBORS.items() for b in bs}
SUPPRESSED = {0,2,7,12}
CORE = {e for e in EDGES if not(set(e)&SUPPRESSED)}
CORE.update({(8,10),(8,13),(1,3),(3,5)})


def covers(vertices, edges):
    for k in range(len(vertices)+1):
        answer = [c for c in itertools.combinations(vertices,k)
                  if all(a in c or b in c for a,b in edges)]
        if answer:
            return answer


def cycles4(vertices, edges):
    found=set()
    for c in itertools.permutations(vertices,4):
        if all(tuple(sorted((c[i],c[(i+1)%4]))) in edges for i in range(4)):
            found.add(min(tuple(c[i:]+c[:i]) for i in range(4)))
    return sorted({min(c,(c[0],c[3],c[2],c[1])) for c in found})


def main():
    vertices = sorted(set(range(14))-SUPPRESSED)
    out = {"target_edges":sorted(EDGES),"core_vertices":vertices,
           "core_edges":sorted(CORE),"core_four_cycles":cycles4(vertices,CORE),
           "minimum_core_vertex_covers":covers(vertices,CORE),
           "minimum_target_vertex_covers":covers(list(range(14)),EDGES)}
    path=Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"core_edges":len(CORE),"cycles4":out["core_four_cycles"],
                      "core_cover_size":len(out["minimum_core_vertex_covers"][0]),
                      "target_cover_size":len(out["minimum_target_vertex_covers"][0]),
                      "path":str(path)}))


if __name__ == "__main__": main()
