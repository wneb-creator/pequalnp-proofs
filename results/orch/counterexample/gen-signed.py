from pathlib import Path
from itertools import combinations
import sys,json
n,s=10,18
R=1<<n;A=R+n+s+2
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
pad=lambda j:p(7,j,0)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target=lambda r:any((r>>a)&1 and (r>>b)&1 for a,b in edges)
F=[]
def add(*c):F.append(c)
for j in range(s):
 add(*(p(0,j,d) for d in range(4)))
 for a,b in combinations(range(4),2):add(-p(0,j,a),-p(0,j,b))
for sd in [1,2]:
 for j in range(s):
  add(*(p(sd,j,k) for k in range(n+j+1)))
  for a,b in combinations(range(n+j+1),2):add(-p(sd,j,a),-p(sd,j,b))
  for r in range(R):
   for k in range(n+j+1):
    sel=p(sd,j,k);v=p(sd+3,j,r)
    if k<n:add(-sel,v if (r>>k)&1 else -v)
    elif k<n+j:
     z=p(3,k-n,r);add(-sel,-v,z);add(-sel,v,-z)
    else:add(-sel,-v)
for j in range(s):
 for r in range(R):
  z,a,b=p(3,j,r),p(4,j,r),p(5,j,r)
  o=p(0,j,0);add(-o,-z,a);add(-o,-z,b);add(-o,z,-a,-b)
  o=p(0,j,1);add(-o,z,-a);add(-o,z,-b);add(-o,-z,a,b)
  o=p(0,j,2);add(-o,-z,a);add(-o,-z,-b);add(-o,z,-a,b)
  o=p(0,j,3);add(-o,-z,-a);add(-o,-z,b);add(-o,z,a,-b)
for r in range(R):add(p(3,s-1,r) if target(r) else -p(3,s-1,r))
for j in range(s):
 add(-pad(j),p(0,j,2));add(-pad(j),p(1,j,n+j));add(-pad(j),p(2,j,n+j))
 add(pad(j),-p(0,j,2),-p(1,j,n+j),-p(2,j,n+j))
 for i in range(j):
  add(-pad(i),-p(1,j,n+i));add(-pad(i),-p(2,j,n+i))
 for a in range(n+j+1):
  for b in range(a+1):add(-p(1,j,a),-p(2,j,b),pad(j))
 add(pad(j),*(p(3,j,r) for r in range(1,R)))
 if j<s-1:
  add(-pad(j+1),pad(j))
  add(pad(j),*(p(sd,k,n+j) for k in range(j+1,s) for sd in [1,2]))
 # Automorphism normal form for the first non-padding gate.
 first=[pad(j)]+([-pad(j-1)] if j else [])
 add(*first,p(1,j,0));add(*first,p(2,j,1),p(2,j,2));add(*first,-p(0,j,3))
# Lexicographic topological ordering of independent consecutive gates.
for j in range(s-1):
 base=[pad(j),pad(j+1),p(1,j+1,n+j),p(2,j+1,n+j)]
 for a in range(n+j+1):
  for b in range(a):add(-p(1,j,a),-p(1,j+1,b),*base)
  for c in range(n+j+1):
   for d in range(c):add(-p(1,j,a),-p(1,j+1,a),-p(2,j,c),-p(2,j+1,d),*base)
   for op1 in range(4):
    for op2 in range(op1):add(-p(1,j,a),-p(1,j+1,a),-p(2,j,c),-p(2,j+1,c),-p(0,j,op1),-p(0,j+1,op2),*base)
out=Path(sys.argv[1])
with out.open('w') as f:
 f.write(f'p cnf {10*(s+1)*A} {len(F)}\n')
 for c in F:f.write(' '.join(map(str,c))+' 0\n')
print(json.dumps({'n':n,'s':s,'rows':R,'clauses':len(F),'vars':10*(s+1)*A,'bytes':out.stat().st_size,'operations':['AND','OR','AND_NOT','NOT_AND']}))
