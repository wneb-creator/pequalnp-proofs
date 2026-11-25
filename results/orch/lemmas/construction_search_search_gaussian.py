from itertools import product,permutations,combinations
import json,time
from pathlib import Path
coords=[(i,j) for i in range(4) for j in range(i,4)]
lookup={ij:k for k,ij in enumerate(coords)}
ix=[[lookup[tuple(sorted((i,j)))] for j in range(4)] for i in range(4)]
terms=[{} for k in range(5)]
for p in permutations(range(4)):
 for k in range(1,5):
  for I in combinations(range(4),k):
   m=tuple(sorted(ix[i][p[i]] for i in I))
   terms[k][m]=terms[k].get(m,0)+1

def q(a):
 rows=[sum(a[ix[i][j]] for j in range(4)) for i in range(4)]
 return sum(v*v*(1 if i==j else 2) for v,(i,j) in zip(a,coords))-2*sum(v*v for v in rows)
def h(a,k):
 return sum(c*prod(a[i] for i in m) for m,c in terms[k].items())
def prod(xs):
 p=1
 for x in xs:p*=x
 return p
def good(a):return q(a)==0 and h(a,3)==0 and h(a,4)==0
def pair(a,b):
 for t in [1,-1,2]:
  c=tuple(t*x+y for x,y in zip(a,b))
  if not good(c):return False
 return True
start=time.time();cand=[]
for a0 in product([-1,0,1,1j,-1j],repeat=9):
 a9=-sum(v*(1 if i==j else 2) for v,(i,j) in zip(a0,coords))
 if a9 not in [-1,0,1,1j,-1j]:continue
 a=a0+(a9,)
 if not any(a):continue
 if next(x for x in a if x)!=1:continue
 if good(a):cand.append(a)
print('candidates',len(cand),'elapsed',time.time()-start,flush=True)
Path('/tmp/oec/pequalnp-pilot-79/gaussian_candidates.json').write_text(json.dumps([[(int(x.real),int(x.imag)) for x in a] for a in cand]))
adj=[set() for a in cand]
for i,a in enumerate(cand):
 for j in range(i):
  if pair(a,cand[j]):adj[i].add(j);adj[j].add(i)
print('edges',sum(map(len,adj))//2,'elapsed',time.time()-start,flush=True)
count=0
for i in range(len(cand)):
 for j in adj[i]:
  if j>=i:continue
  for k in adj[i]&adj[j]:
   if k>=j:continue
   count+=1
   A=[cand[x] for x in [i,j,k]]
   if any(not good(tuple(a+r*b+s*c for a,b,c in zip(*A))) for r,s in product([-2,-1,1,2],repeat=2)):continue
   import sympy
   if sympy.Matrix(A).rank()!=3:continue
   print('FOUND',A,flush=True)
print('triangles',count,'elapsed',time.time()-start,flush=True)
