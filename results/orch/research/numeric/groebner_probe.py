from pathlib import Path
import itertools,json,time,sys,resource
import sympy as sp
from sympy.polys.rings import ring
from sympy.polys.groebnertools import groebner
resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
BASE=Path('/tmp/oec/pequalnp-pilot-78/numeric')
pivots=tuple(map(int,sys.argv[1].split(','))) if len(sys.argv)>1 else (0,4,7)
prime=int(sys.argv[2]) if len(sys.argv)>2 else 101
method=sys.argv[3] if len(sys.argv)>3 else 'f5b'
coords=[(i,j) for i in range(4) for j in range(i,4)];lookup={p:k for k,p in enumerate(coords)}
w=[1 if i==j else 2 for i,j in coords]
dep=next(i for i,(r,c) in enumerate(coords) if r==c and i not in pivots)
free=[i for i in range(10) if i not in pivots and i!=dep]
R,*xs=ring(','.join('x'+str(i) for i in range(18)),sp.QQ if not prime else sp.GF(prime),order='grevlex')
U=[[R.zero for _ in range(3)] for _ in range(10)]
for j,p in enumerate(pivots):U[p][j]=R.one
for k,i in enumerate(free):U[i]=xs[3*k:3*k+3]
for j in range(3):U[dep][j]=-sum((w[i]*U[i][j] for i in range(10)),R.zero)
exps=[e for d in range(5) for e in itertools.product(range(d+1),repeat=3) if sum(e)==d]
coeff={e:R.zero for e in exps};start=time.monotonic()
for perm in itertools.permutations(range(4)):
 cs=[lookup[tuple(sorted((r,perm[r])))] for r in range(4)]
 for choice in itertools.product(range(4),repeat=4):
  term=R.one
  for r,k in enumerate(choice):
   if k:term*=U[cs[r]][k-1]
   if not term:break
  if term:coeff[tuple(choice.count(k) for k in (1,2,3))]+=term
assert coeff[(0,0,0)]==R(24)
assert all(not v for e,v in coeff.items() if sum(e)==1)
polys=[v.monic() for e,v in coeff.items() if sum(e)>=2 and v]
print(json.dumps({'stage':'generated','pivots':pivots,'domain':str(R.domain),'method':method,'seconds':time.monotonic()-start,'polynomials':len(polys),'terms':sum(len(p) for p in polys),'max_terms':max(map(len,polys))}),flush=True)
G=groebner(polys,R,method=method)
print(json.dumps({'stage':'completed','seconds':time.monotonic()-start,'basis_size':len(G),'unit_ideal':len(G)==1 and G[0]==R.one,'basis_terms':sum(map(len,G)),'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}),flush=True)
if len(G)==1 and G[0]==R.one:
 (BASE/(f'unit-{prime}-{method}-'+str(pivots)+'.txt')).write_text('1\n')
