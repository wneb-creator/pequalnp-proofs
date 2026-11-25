import sympy as s,itertools,json,collections
from sympy.polys.matrices import DomainMatrix
from pathlib import Path
K=s.QQ.algebraic_field(s.sqrt(2));zero=K.zero;one=K.one
ij=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)];index={pair:i for i,pair in enumerate(ij)}
terms=[[index[tuple(sorted((i,j)))] for i,j in enumerate(p)] for p in itertools.permutations(range(4))]
def rank(a):return DomainMatrix(a,(len(a),len(a[0])),K).rank()
def gradient(A,B,x,y):
 v=[one+x*a+y*b for a,b in zip(A,B)];g=[zero]*10
 for t in terms:
  for r in range(4):
   z=one
   for k in range(4):
    if k!=r:z*=v[t[k]]
   g[t[r]]+=z
 return g
def tangent(A,B):
 e=[gradient(A,B,i,j) for d in range(4) for i in range(d+1) for j in [d-i]]
 dm=[]
 for d in range(1,5):
  for i in range(d+1):
   j=d-i;g=gradient(A,B,i,j);dm.append([i*x for x in g]+[j*x for x in g])
 return (10-rank(e),10-rank(e+[[one]+[zero]*9]),20-rank(dm)-4,20-rank(dm+[[one]+[zero]*19,[zero]*10+[one]+[zero]*9])-4)
def vector(M,p=None):
 if p is None:p=range(4)
 return [K.from_sympy(s.sympify(M[p[i]][p[j]])) for i,j in ij]
q=s.sqrt(2)
A=[[0,1,-1,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0]]
B=[[-1+q,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,-1-q]]
print('sqrt2 family1 (extension, slice extension, global Fano tangent, slice Fano tangent)',tangent(vector(A,[1,0,2,3]),vector(B,[1,0,2,3])))
A=[[0,0,0,1],[0,0,0,1],[0,0,0,-2],[1,1,-2,0]]
B=[[-1+q,1,0,0],[1,-1-q,0,0],[0,0,0,0],[0,0,0,0]]
print('sqrt2 family2 (extension, slice extension, global Fano tangent, slice Fano tangent)',tangent(vector(A,[2,0,1,3]),vector(B,[2,0,1,3])))
planes=json.loads(Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_planes.json').read_text());counts=collections.Counter()
for plane in planes:
 rows=[]
 for r in plane['rref']:
  v=[zero]*10
  for k,x in zip([1,2,3,5,6,8],r):v[k]=K.from_sympy(s.sympify(x))
  rows.append(v)
 counts[tangent(*rows)]+=1
print('hollow exact distributions',dict(counts))
