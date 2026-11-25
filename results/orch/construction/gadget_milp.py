import sys, time, json
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
k=int(sys.argv[1]); gates=int(sys.argv[2]); n=2*k+1
# true on matching edges p_i*y_i or common t*p_i.
# false whenever <=2 points selected and no edge.
rows=[]
for x in range(1<<n):
 p=[(x>>i)&1 for i in range(k)]; ys=[(x>>(k+i))&1 for i in range(k)]; t=(x>>(2*k))&1
 yes=any(p[i] and (ys[i] or t) for i in range(k))
 if yes or sum(p)<=2: rows.append((x,int(yes)))
N=len(rows); vcount=0; low=[]; high=[]
def var(lo=0,hi=1):
 global vcount
 i=vcount; vcount+=1; low.append(lo);high.append(hi);return i
ops=[var() for g in range(gates)]
a=[[var() for j in range(n+g)] for g in range(gates)]
b=[[var() for j in range(n+g)] for g in range(gates)]
A=[[var() for t in range(N)] for g in range(gates)]
B=[[var() for t in range(N)] for g in range(gates)]
V=[[var(y,y) if g==gates-1 else var() for x,y in rows] for g in range(gates)]
ri=[];ci=[];da=[];cl=[];cu=[]
def cons(d,lo=-np.inf,hi=np.inf):
 r=len(cl)
 for i,c in d.items():
  if c:ri.append(r);ci.append(i);da.append(c)
 cl.append(lo);cu.append(hi)
for g in range(gates):
 cons({j:1 for j in a[g]},1,1);cons({j:1 for j in b[g]},1,1)
 cons({**{j:i for i,j in enumerate(a[g])},**{j:-i for i,j in enumerate(b[g])}},hi=0)
 for t,(x,y) in enumerate(rows):
  for picks,z in [(a[g],A[g][t]),(b[g],B[g][t])]:
   for j,s in enumerate(picks):
    if j<n:
     bit=(x>>j)&1
     cons({z:1,s:1},hi=1+bit);cons({z:1,s:-1},lo=bit-1)
    else:
     w=V[j-n][t]
     cons({z:1,w:-1,s:1},hi=1);cons({z:1,w:-1,s:-1},lo=-1)
  v=V[g][t]; aa=A[g][t]; bb=B[g][t]; op=ops[g]
  cons({v:1,aa:-1,op:1},hi=1);cons({v:1,bb:-1,op:1},hi=1)
  cons({v:1,aa:-1,bb:-1,op:-1},lo=-2)
  cons({v:1,aa:-1,op:1},lo=0);cons({v:1,bb:-1,op:1},lo=0)
  cons({v:1,aa:-1,bb:-1,op:-1},hi=0)
mat=coo_matrix((da,(ri,ci)),shape=(len(cl),vcount)).tocsc()
print(dict(k=k,gates=gates,rows=N,vars=vcount,constraints=len(cl)),flush=True)
res=milp(np.zeros(vcount),integrality=np.ones(vcount),bounds=Bounds(low,high),constraints=LinearConstraint(mat,cl,cu),options={'disp':True,'time_limit':180})
print(res,flush=True)
if res.x is not None:
 result=[]
 for g in range(gates):
  result.append(('and' if res.x[ops[g]]>.5 else 'or',int(np.argmax(res.x[a[g]])),int(np.argmax(res.x[b[g]]))))
 print(json.dumps(result),flush=True)
