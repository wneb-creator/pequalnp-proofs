from itertools import combinations
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import lil_matrix

E=[(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
D={tuple(sorted(e)):i for i,e in enumerate(E)}
BC=[]
for a in range(1,128):
 for b in range(a+1,128):
  if a&b:continue
  A=[i for i in range(7) if a>>i&1];B=[i for i in range(7) if b>>i&1]
  pairs=[tuple(sorted((i,j))) for i in A for j in B]
  if all(p in D for p in pairs):
   mask=sum(1<<D[p] for p in pairs)
   BC.append((mask,a,b))
variables=[];costs=[]
def variable(name,cost=0):
 i=len(variables);variables.append(name);costs.append(cost);return i
X={s:variable(('or',s),int(s.bit_count()>1)) for s in range(1,128)}
Y={}
for s in range(1,128):
 for a in range(1,s):
  b=s^a
  if a&s==a and a<b:
   Y[s,a,b]=variable(('split',s,a,b))
Z=[variable(('biclique',k),2) for k in range(len(BC))]
constraints=[]
def constraint(row,lo=-np.inf,hi=np.inf):constraints.append((row,lo,hi))
for s in range(1,128):
 if s.bit_count()==1:constraint({X[s]:1},1,1)
 else:
  row={X[s]:-1}
  for (t,a,b),y in Y.items():
   if s==t:row[y]=1
  constraint(row,0,0)
for (s,a,b),y in Y.items():
 constraint({y:1,X[a]:-1},hi=0)
 constraint({y:1,X[b]:-1},hi=0)
for k,(mask,a,b) in enumerate(BC):
 constraint({Z[k]:1,X[a]:-1},hi=0)
 constraint({Z[k]:1,X[b]:-1},hi=0)
for e in range(12):constraint({Z[k]:1 for k,(mask,a,b) in enumerate(BC) if mask>>e&1},lo=1)
mat=lil_matrix((len(constraints),len(variables)))
for i,(row,lo,hi) in enumerate(constraints):
 for j,v in row.items():mat[i,j]=v
r=milp(np.array(costs),integrality=np.ones(len(variables)),bounds=Bounds(0,1),constraints=LinearConstraint(mat.tocsr(),[c[1] for c in constraints],[c[2] for c in constraints]),options={'time_limit':300})
print(r.message,flush=True)
if r.x is not None:
 print('circuit size',r.fun-1,flush=True)
 for i,v in enumerate(r.x):
  if v>.9:
   name=variables[i]
   if name[0]=='biclique':print(name,BC[name[1]])
   else:print(name)
