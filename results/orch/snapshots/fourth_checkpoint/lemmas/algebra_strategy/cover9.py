import itertools,json
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import csc_matrix
base=Path("results/orch/lemmas")
case=json.loads((base/"algebra_strategy/k9_arc_4_8_10_12.json").read_text())
edges=sorted(set(map(tuple,case["edges"]))|{(0,16),(2,9),(2,12),(2,18)})
neighbor=[{b for a,b in edges if a==r}for r in range(9)]
rect=[]
for rowmask in range(1,512):
 rows=[r for r in range(9)if rowmask>>r&1]
 common=sorted(set.intersection(*(neighbor[r]for r in rows)))
 for cmask in range(1,1<<len(common)):
  cols=[c for j,c in enumerate(common)if cmask>>j&1]
  es={ (r,c)for r in rows for c in cols}
  rect.append((rows,cols,es,len(rows)+len(cols)))
A=csc_matrix(np.array([[int(e in t[2])for t in rect]for e in edges],dtype=float))
r=milp(np.array([t[3]for t in rect],dtype=float),integrality=np.ones(len(rect)),bounds=Bounds(0,1),constraints=LinearConstraint(A,np.ones(len(edges)),np.full(len(edges),np.inf)),options={"time_limit":10.0,"mip_rel_gap":0.0,"disp":True})
print("edges",len(edges),"rectangles",len(rect),"status",r.status,"message",r.message)
print("objective",r.fun,"dual",getattr(r,"mip_dual_bound",None))
if r.x is not None:
 selected=[i for i,x in enumerate(r.x)if x>0.5]
 result={"objective":float(r.fun),"status":int(r.status),"rectangles":[{"rows":rect[i][0],"lines":rect[i][1]}for i in selected]}
 (base/"algebra_strategy/cover9-result.json").write_text(json.dumps(result,indent=2))
 print(json.dumps(result))
