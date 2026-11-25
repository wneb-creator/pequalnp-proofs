import json,time
from fractions import Fraction as F
from pathlib import Path
import sympy as s
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh');start=time.monotonic()
d=json.loads((base/'zero-edge-pencil.json').read_text());h=json.loads((base/'zero-edge-high-precision.json').read_text())
vs=s.symbols(' '.join(d['variables']));polys=[s.Poly(s.sympify(t),*vs) for t in d['equations']]
zero=(F(0),F(0));one=(F(1),F(0))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def sc(c,a):return(c*a[0],c*a[1])
def norm(a):return abs(a[0])+abs(a[1])
def summ(vals):
 r=zero
 for a in vals:r=add(r,a)
 return r
z=[(F(a),F(b)) for a,b in zip(h['real'],h['imag'])]
R=[[(F(h['inverse_real'][i][j]),F(h['inverse_imag'][i][j])) for j in range(12)] for i in range(12)]
zp=[]
for a in z:
 ps=[one]
 for k in range(4):ps.append(mul(ps[-1],a))
 zp.append(ps)
def evaluate(poly):
 ans=zero
 for ex,co in poly.terms():
  term=(F(int(co.p),int(co.q)),F(0))
  for j,n in enumerate(ex):
   if n:term=mul(term,zp[j][n])
  ans=add(ans,term)
 return ans
F0=[evaluate(p) for p in polys]
J=[[evaluate(p.diff(v)) for v in vs] for p in polys]
RF=[summ(mul(R[i][j],F0[j]) for j in range(12)) for i in range(12)]
eps=max(map(norm,RF))
RJ=[[summ(mul(R[i][k],J[k][j]) for k in range(12)) for j in range(12)] for i in range(12)]
eta=max(sum(norm(add((one if i==j else zero),neg(RJ[i][j]))) for j in range(12)) for i in range(12))
radius=F(1,10**20);bounds=[norm(a)+radius for a in z]
bp=[[b**k for k in range(5)] for b in bounds]
Hs=[]
for poly in polys:
 H=F(0)
 for ex,co in poly.terms():
  for i in range(12):
   for j in range(12):
    count=ex[i]*(ex[j]-(1 if i==j else 0))
    if count<=0:continue
    term=abs(F(int(co.p),int(co.q)))*count
    for k,n in enumerate(ex):term*=bp[k][n-(1 if k==i else 0)-(1 if k==j else 0)]
    H+=term
 Hs.append(H)
M=max(sum(norm(R[i][k])*Hs[k] for k in range(12)) for i in range(12))
contraction=eta+M*radius
assert contraction<F(1,2)
assert eps+contraction*radius<radius
# Diagonal minor rows0,1 equals z0*z3-z1*z2. Its real part stays nonzero.
minor=add(mul(z[0],z[3]),neg(mul(z[1],z[2])))
minor_error=radius*(norm(z[0])+norm(z[3])+norm(z[1])+norm(z[2]))+2*radius*radius
assert abs(minor[0])>minor_error
# RJ is invertible because eta<1, so R is invertible; fixed point implies F=0.
assert eta<1
values={'radius':radius,'newton_residual_bound':eps,'inverse_error_bound':eta,'jacobian_lipschitz_bound':M,'contraction_bound':contraction,'minor_real_center':minor[0],'minor_variation_bound':minor_error}
out={k:str(v) for k,v in values.items()}
out['scope']='Exact rational inequalities certify by Banach contraction a complex zero-edge constant-permanent pencil with nonzero diagonal minor01. This is a mathematical existence argument, not Lean checked and not a three-plane witness.'
(base/'zero-edge-rational-certificate.json').write_text(json.dumps(out,indent=2))
for k,v in values.items():print(k,'APPROX',float(v),flush=True)
print('RATIONAL_INEQUALITIES_PASS','SECONDS',time.monotonic()-start,flush=True)
