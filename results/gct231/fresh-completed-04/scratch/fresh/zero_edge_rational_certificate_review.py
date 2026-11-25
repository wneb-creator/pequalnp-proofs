"""Independent exact rational replay using explicit differentiated polynomials."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,json
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
paths={name:base/name for name in ['zero-edge-pencil.json','zero-edge-high-precision.json','zero-edge-rational-certificate.json','zero_edge_rational_certificate.py']}
hashes={name:hashlib.sha256(p.read_bytes()).hexdigest() for name,p in paths.items()}
assert hashes['zero-edge-pencil.json']=='68694af7231339f727f58f0ecee44361318f2e7161335daa60b1c7089e528f3b'
for name,digest in hashes.items():print('SHA256',name,digest,flush=True)
data=json.loads(paths['zero-edge-pencil.json'].read_text())
hi=json.loads(paths['zero-edge-high-precision.json'].read_text())
saved=json.loads(paths['zero-edge-rational-certificate.json'].read_text())
variables=s.symbols('v0:12')
assert data['variables']==list(map(str,variables)) and len(data['equations'])==12
assert len(hi['real'])==len(hi['imag'])==12
assert len(hi['inverse_real'])==len(hi['inverse_imag'])==12
assert all(len(row)==12 for row in hi['inverse_real']+hi['inverse_imag'])
polys=[s.Poly(s.sympify(eq),*variables,domain=s.QQ) for eq in data['equations']]
assert sorted(p.total_degree() for p in polys)==[2]*3+[3]*4+[4]*5
Jpolys=[[p.diff(v) for v in variables] for p in polys]
center=list(zip(map(Fraction,hi['real']),map(Fraction,hi['imag'])))
R=[[tuple(map(Fraction,[hi['inverse_real'][i][j],hi['inverse_imag'][i][j]])) for j in range(12)] for i in range(12)]
zero=(Fraction(0),Fraction(0));one=(Fraction(1),Fraction(0))
def plus(z,w):return z[0]+w[0],z[1]+w[1]
def times(z,w):return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]
def abs1(z):return abs(z[0])+abs(z[1])
def total(values):
 result=zero
 for z in values:result=plus(result,z)
 return result
def rational(c):return Fraction(int(c.p),int(c.q))
powers=[]
for z in center:
 row=[one]
 for _ in range(4):row.append(times(row[-1],z))
 powers.append(row)
def evaluate(poly):
 values=[]
 for ex,c in poly.terms():
  value=(rational(c),Fraction(0))
  for i,n in enumerate(ex):value=times(value,powers[i][n])
  values.append(value)
 return total(values)
F0=list(map(evaluate,polys))
J0=[[evaluate(p) for p in row] for row in Jpolys]
epsilon=max(abs1(total(times(R[i][k],F0[k]) for k in range(12))) for i in range(12))
errors=[]
for i in range(12):
 row=[]
 for j in range(12):
  value=total(times(R[i][k],J0[k][j]) for k in range(12))
  row.append(plus((Fraction(int(i==j)),Fraction(0)),(-value[0],-value[1])))
 errors.append(row)
eta=max(sum(map(abs1,row)) for row in errors)
radius=Fraction(1,10**20)
bounds=[abs1(z)+radius for z in center]
bound_powers=[[b**i for i in range(5)] for b in bounds]
def polynomial_abs_bound(poly):
 value=Fraction(0)
 for ex,c in poly.terms():
  term=abs(rational(c))
  for i,n in enumerate(ex):term*=bound_powers[i][n]
  value+=term
 return value
# Differentiate first, then bound each second derivative separately.
Hbounds=[sum(polynomial_abs_bound(Jpolys[k][i].diff(variables[j]))
             for i in range(12) for j in range(12)) for k in range(12)]
M=max(sum(abs1(R[i][k])*Hbounds[k] for k in range(12)) for i in range(12))
kappa=eta+M*radius
minor=plus(times(center[0],center[3]),tuple(-v for v in times(center[1],center[2])))
minor_variation=radius*sum(abs1(center[i]) for i in (0,1,2,3))+2*radius**2
values={'radius':radius,'newton_residual_bound':epsilon,'inverse_error_bound':eta,
        'jacobian_lipschitz_bound':M,'contraction_bound':kappa,
        'minor_real_center':minor[0],'minor_variation_bound':minor_variation}
for name,value in values.items():
 assert value==Fraction(saved[name]),name
 print('EXACT_MATCH',name,'approx',float(value),flush=True)
assert eta<1 and kappa<Fraction(1,2)
assert epsilon+kappa*radius<radius
assert abs(minor[0])>minor_variation
print('Strict rational invertibility, contraction, self-map and nonzero-minor inequalities: PASS',flush=True)
print('Polynomial lineage is the independently Ryser-verified12-coefficient normalized pencil source',flush=True)
assert all(hashlib.sha256(path.read_bytes()).hexdigest()==hashes[name] for name,path in paths.items())
out={'source_hashes':hashes,'computed_values':{k:str(v) for k,v in values.items()},
     'norm':'max over coordinates of abs(real)+abs(imag)',
     'scope':'Exact Banach certificate for a two-dimensional zero-edge pencil with diagonal rank2; not a three-plane witness and not Lean checked.'}
(base/'zero-edge-rational-independent-review.json').write_text(json.dumps(out,indent=2)+'\n')
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
