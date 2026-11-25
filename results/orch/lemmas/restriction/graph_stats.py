import json
from pathlib import Path
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def independence(vertices,ed):
    good=[]
    for mask in range(1<<len(vertices)):
        s={v for i,v in enumerate(vertices) if mask>>i&1}
        if all(not(a in s and b in s) for a,b in ed): good.append(s)
    alpha=max(map(len,good))
    return alpha,len(vertices)-alpha,sum(len(s)==alpha for s in good)
rows=[]
for v in range(10):
    verts=[u for u in range(10) if u!=v]
    e0=[(a,b) for a,b in edges if v not in (a,b)]
    alpha,tau,num=independence(verts,e0)
    neigh={b if a==v else a for a,b in edges if v in (a,b)}
    rem=[u for u in range(10) if u!=v and u not in neigh]
    er=[(a,b) for a,b in edges if a in rem and b in rem]
    degrees={u:sum(u in e for e in er) for u in rem}
    rows.append(dict(vertex=v,zero_cofactor_edges=len(e0),zero_cofactor_alpha=alpha,
      zero_cofactor_vertex_cover=tau,zero_cofactor_star_upper=len(e0)+tau-1,
      one_cofactor_neighbors=sorted(neigh),one_cofactor_residual_vertices=rem,
      one_cofactor_residual_edges=er,one_cofactor_residual_degrees=degrees))
print(json.dumps(rows,indent=2))
