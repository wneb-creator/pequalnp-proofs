"""Generate the independent four-row-anchor model over a splitting prime.

The matrices B_v sum to J. Row v of B_v has offdiagonals zero and diagonal
lambda_v weight_v. The five remaining diagonal parameters solve the row and
column sum equations on the bipartite cube by a spanning tree.
"""
from pathlib import Path
from itertools import permutations,combinations,product
from collections import defaultdict
import sys,re,time
from sympy.polys.rings import ring
from sympy.polys.domains import GF
p=int(sys.argv[1]);indices=tuple(map(int,sys.argv[2]));mode=sys.argv[3];J=Path('/tmp/oec/pequalnp-pilot-79');st=time.time()
roots=[x for x in range(p) if (x**4-16*x**3+72*x*x-96*x+24)%p==0];assert len(roots)==4
lam=[roots[i] for i in indices];I=list(range(4));pairs=list(combinations(I,2))
vs=['d'+str(i) for i in range(5)]+['e'+str(i)+str(j) for i,j in pairs]+['w0','w1','w2'];R,*V=ring(','.join(vs),GF(p));v=dict(zip(vs,V));zero,one=R.zero,R.one
wt=[v['w'+str(i)] for i in range(3)];wt.append(1-sum(wt))
M=[[[zero for _ in I] for _ in I] for _ in I]
for i,j in pairs:
 k,l=[t for t in I if t not in [i,j]];x=v['e'+str(i)+str(j)]
 M[k][i][j]=M[k][j][i]=x;M[l][i][j]=M[l][j][i]=1-x
for i in I:M[i][i][i]=lam[i]*wt[i]
rhs=[(16-lam[i])*wt[i]-2*sum(M[i][a][b] for a,b in pairs) for i in I]+[1-lam[j]*wt[j] for j in I]
# Connect all 8 vertices before using the 5 remaining degree-of-freedom edges.
par=list(range(8));tree=[];free=[]
def find(i):
 while par[i]!=i:i=par[i]
 return i
for i,j in product(I,repeat=2):
 if i==j:continue
 u,w=find(i),find(j+4)
 if u!=w:par[u]=w;tree.append((i,j))
 else:free.append((i,j))
assert len(tree)==7 and len(free)==5
for n,(i,j) in enumerate(free):f=v['d'+str(n)];M[i][j][j]=f;rhs[i]-=f;rhs[j+4]-=f
while tree:
 for k in range(8):
  inc=[(i,j) for i,j in tree if k==i or k==j+4]
  if len(inc)==1:break
 else:raise ValueError('no leaf')
 i,j=inc[0];f=rhs[k];M[i][j][j]=f;rhs[i]-=f;rhs[j+4]-=f;tree.remove((i,j))
assert not any(rhs)
assert all(sum(M[k][i][j] for k in I)==one for i,j in product(I,repeat=2))
assert all(sum(sum(row) for row in M[i])==16*wt[i] for i in I)
polys=[]
def push(f):
 if not f:return
 lc=f.LC
 f=f.quo_ground(lc)
 if f not in polys:polys.append(f)
# Each vertex has the exact cubic rook polynomial prod_{r != anchor root}(z+lambda_r*w).
# Its degree2 coefficient is the prescribed trace (already encoded), leaving quadratic and cubic equations.
for i in I:
 other=[x for x in I if x!=i];rr=roots[:];rr.remove(lam[i])
 q=sum(M[i][a][c]*M[i][b][d]+M[i][a][d]*M[i][b][c] for a,b in combinations(other,2) for c,d in combinations(other,2))
 f=sum(M[i][other[0]][order[0]]*M[i][other[1]][order[1]]*M[i][other[2]][order[2]] for order in permutations(other))
 push(q-(rr[0]*rr[1]+rr[1]*rr[2]+rr[0]*rr[2])*wt[i]**2);push(f-rr[0]*rr[1]*rr[2]*wt[i]**3)
# Use three coordinates B_i-w_i J for L, centered at J; J=sum B_i.
T=[[[M[k][i][j]-wt[k] for j in I] for i in I] for k in range(3)]
def addc(poly,ids,term):
 if term:poly[ids]=poly.get(ids,zero)+term
for deg in [2,3,4]:
 ff={}
 for pm in permutations(I):
  for rows in combinations(I,deg):
   for ix in product(range(3),repeat=deg):
    c=one
    for j,k in zip(rows,ix):c*=T[k][j][pm[j]]
    addc(ff,tuple(sorted(ix)),c)
 for ix,g in sorted(ff.items()):push(g)
tag='_'.join(sys.argv[1:]);out=J/('fresh_laguerre_frame_'+tag+'.msolve')
with out.open('w') as f:
 f.write(','.join(vs)+'\n'+str(p)+'\n'+',\n'.join(re.sub(r'\s*mod\s*'+str(p)+r'\b','',str(g)).replace('**','^').replace(' ','') for g in polys)+'\n')
print('prime',p,'roots',roots,'choices',lam,'free diagonal edges',free,'variables',len(vs),'polynomials',len(polys),'terms',sum(map(len,polys)),'lengths',[(max(sum(e) for e in g),len(g)) for g in polys],'sec',time.time()-st)
