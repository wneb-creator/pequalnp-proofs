import sympy as s,itertools,json,time
from pathlib import Path
b=Path(__file__).parent;d=json.loads((b/'stabilizer-fast.json').read_text());x=s.symbols(d['variables']);loc=dict(zip(d['variables'],x));a,bb,c,u,v,w,p,q,r=x
T=s.Matrix([[a,u,v,w],[u,bb,p,q],[v,p,c,r],[w,q,r,-a-bb-c-2*(u+v+w+p+q+r)]])
Q,C,F=[s.sympify(d[n],locals=loc) for n in ['quadratic','cubic','quartic']]
tr=s.trace(T);rows=[sum(T[i,j] for j in range(4)) for i in range(4)]
inv=[tr**2,sum(T[i,i]**2 for i in range(4)),sum(T[i,j]**2 for i in range(4) for j in range(i+1,4)),sum(T[i,i]*rows[i] for i in range(4)),sum(t*t for t in rows)]
cols=[s.Poly(s.expand(inv[i]*inv[j]),*x) for i,j in itertools.combinations_with_replacement(range(5),2)]+[s.Poly(s.expand(tr*C),*x),s.Poly(F,*x)]
D=s.Poly(T.det(),*x);mons=sorted(set(D.monoms()).union(*(set(z.monoms()) for z in cols)))
mat=s.Matrix([[z.coeff_monomial(m) for z in cols]+[D.coeff_monomial(m)] for m in mons]);prime=1009
basis={};rank=[]
for j in range(mat.cols):
 v=[int(z)%prime for z in mat[:,j]]
 for k,old in sorted(basis.items()):
  if v[k]:
   v=[(a-v[k]*bb)%prime for a,bb in zip(v,old)]
 k=next((k for k,t in enumerate(v) if t),None)
 if k is not None:
  z=pow(v[k],-1,prime);basis[k]=[(z*a)%prime for a in v]
 rank.append(len(basis))
print('invariantproducts+traceC+F rank',rank[-2],'augmentedwithdet rank',rank[-1],flush=True)
if rank[-2]==rank[-1]:
 sol=s.linsolve((mat[:,:-1],mat[:,-1]));print('EXACT_RELATION',sol,flush=True)
