from pathlib import Path
import json

edges={(min(a,b),max(a,b)) for a,b in [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]}
def adjacent(a,b):
    return (min(a,b),max(a,b)) in edges

automorphisms=[]
def visit(images):
    if len(images)==10:
        automorphisms.append(tuple(images))
        return
    u=len(images)
    for v in range(10):
        if v not in images and all(adjacent(u,i)==adjacent(v,images[i]) for i in range(u)):
            visit(images+[v])
visit([])
edge_orbit={tuple(sorted((p[0],p[1]))) for p in automorphisms}
nonedge_orbit={tuple(sorted((p[0],p[2]))) for p in automorphisms}
all_pairs={(a,b) for a in range(10) for b in range(a+1,10)}
assert edge_orbit==edges
assert nonedge_orbit==all_pairs-edges
result={'automorphism_count':len(automorphisms),'edge_representative':[0,1],'edge_orbit_size':len(edge_orbit),'nonedge_representative':[0,2],'nonedge_orbit_size':len(nonedge_orbit),'scope':'Finite Python computation only; neither this symmetry argument nor the search is Lean-checked.'}
Path('/tmp/oec/pequalnp-pilot-93/prefix_symmetry.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
