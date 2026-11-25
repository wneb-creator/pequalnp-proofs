from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sympy as s
base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
p,q,r,a,b,x,y=s.symbols('p q r a b x y');loc={str(v):v for v in(p,q,r,a,b,x,y)}
parse=lambda z:s.sympify(z,locals=loc)
d=json.loads((base/'star-pencil-five.json').read_text());low=json.loads((base/'star-lowdegree.json').read_text())
M=s.Matrix([[parse(v) for v in row] for row in d['matrix']]);w=a*x+b*y
want=s.diag(-p*x-q*y-r*w-2*(x+y+w),p*x,q*y,r*w)
for j,v in enumerate([x,y,w],1):want[0,j]=want[j,0]=v
assert M==want and M==M.T and s.expand(sum(M))==0
N=s.ones(4)+M
per=0
for mask in range(1,16):
 cols=[j for j in range(4) if mask>>j&1]
 per+=(-1)**(4-len(cols))*s.prod(sum(N[i,j] for j in cols) for i in range(4))
poly=s.Poly(s.expand(per-24),x,y);rows={tuple(z['monomial']):parse(z['coefficient']) for z in d['equations']}
assert set(rows)==set(poly.monoms())
for mon,c in rows.items():assert s.expand(c-poly.coeff_monomial(mon))==0
print('All16 star matrix entries, tangent, and all10 coefficient rows independently verified by Ryser: PASS',flush=True)
assert low['unknowns']==d['unknowns']==['p','q','r','a','b'] and low['nonzero_assumptions']==['a','b']
assert [z['monomial'] for z in low['equations'][:6]]==[[2,2],[2,1],[2,0],[1,2],[1,1],[0,2]]
for z in low['equations'][:6]:assert s.expand(parse(z['coefficient'])-rows[tuple(z['monomial'])])==0
Ep=-a*r*(r*r+2*r-1)+p*(2*r-1)+2*r;Eq=Ep.xreplace({a:b,p:q})
assert s.expand(parse(low['equations'][6]['coefficient'])-Ep)==0
assert s.expand(parse(low['equations'][7]['coefficient'])-Eq)==0
assert s.expand(2*a*a*Ep-a*r*rows[(2,0)]+2*rows[(3,0)])==0
assert s.expand(2*b*b*Eq-b*r*rows[(0,2)]+2*rows[(0,3)])==0
print('Exact E identities:2a^2 Ep=a*r*Q20-2*C30 and2b^2 Eq=b*r*Q02-2*C03: PASS',flush=True)
print('Only a,b nonzero is needed to deduce E=0; no division by2r-1. Retained quartic is x^2*y^2.',flush=True)
assert len(low['equations'])==8 and sum(len(s.Poly(parse(z['coefficient']),p,q,r,a,b).terms()) for z in low['equations'])==78
print('Lowdegree export8rows/5variables/78terms: PASS',flush=True)
assert s.expand(poly.as_expr().subs({p:0,q:0,r:0,a:-1,b:-1}))==0
print('Known zero-diagonal star pencil p=q=r=0,a=b=-1 satisfies the full permanent identity. This source review does not independently certify the reported ideal classification.',flush=True)
print('Geometry: for each leaf, vanishing of its diagonal on the kernel of its nonzero edge linear form yields the corresponding scalar p/q/r. Choosing two independent leaf edges as x,y yields this form. Review is conditional on star support and a,b nonzero; no coverage of other support strata.',flush=True)
print('Hashes',json.dumps({name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in ['star_pencil.py','star-pencil-five.json','star-lowdegree.json']}),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
