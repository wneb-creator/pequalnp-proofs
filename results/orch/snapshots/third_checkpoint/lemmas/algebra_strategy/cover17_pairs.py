import itertools,json
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
base=Path("results/orch/lemmas")
case=json.loads((base/"circuit_search/subsets/k6_p3.json").read_text())
edges=sorted(set(map(tuple,case["edges"]))|{(0,11),(2,6),(2,9),(2,13)})
neighbor=[{b for a,b in edges if a==r}for r in range(6)]
rect=[]
for rowmask in range(1,64):
 rows=[r for r in range(6)if rowmask>>r&1]
 common=sorted(set.intersection(*(neighbor[r]for r in rows)))
 for cmask in range(1,1<<len(common)):
  cols=[c for j,c in enumerate(common)if cmask>>j&1]
  rect.append((rows,cols,{(r,c)for r in rows for c in cols},len(rows)+len(cols)))
pairs=sorted(set(p for rows,cols,_,_ in rect for S in (rows,cols)for p in itertools.combinations(S,2)))
yindex={p:len(rect)+i for i,p in enumerate(pairs)}
z=[]
for i,(rows,cols,_,_)in enumerate(rect):
 for S in(rows,cols):
  for p in itertools.combinations(S,2):z.append((i,p))
zindex={v:len(rect)+len(pairs)+i for i,v in enumerate(z)}
n=len(rect)+len(pairs)+len(z)
c=np.array([r[3]for r in rect]+[1]*len(pairs)+[-1]*len(z),dtype=float)
rr=[];cc=[];vv=[];lower=[];upper=[]
def constraint(entries,lo,hi):
 row=len(lower)
 for col,value in entries:rr.append(row);cc.append(col);vv.append(value)
 lower.append(lo);upper.append(hi)
for edge in edges:constraint([(i,1)for i,r in enumerate(rect)if edge in r[2]],1,np.inf)
for i,p in z:constraint([(zindex[i,p],1),(yindex[p],-1)],-np.inf,0)
for i,(rows,cols,_,_)in enumerate(rect):
 for e in rows+cols:
  opts=[(zindex[i,p],1)for j,p in z if j==i and e in p]
  if opts:constraint(opts+[(i,-1)],-np.inf,0)
A=coo_matrix((vv,(rr,cc)),shape=(len(lower),n)).tocsc()
r=milp(c,integrality=np.ones(n),bounds=Bounds(0,1),constraints=LinearConstraint(A,lower,upper),options={"time_limit":10.0,"mip_rel_gap":0.0,"disp":True})
print("variables",n,"status",r.status,"objective",r.fun,"dual",getattr(r,"mip_dual_bound",None))
if r.x is not None:
 selected=[i for i in range(len(rect))if r.x[i]>.5]
 result={"objective":float(r.fun),"status":int(r.status),"gates_before_final_adjustment":float(r.fun)-1,"rectangles":[{"rows":rect[i][0],"lines":rect[i][1],"pairs":[list(p)for j,p in z if j==i and r.x[zindex[j,p]]>.5]}for i in selected]}
 (base/"algebra_strategy/cover17-pairs-result.json").write_text(json.dumps(result,indent=2))
 print(json.dumps(result))
