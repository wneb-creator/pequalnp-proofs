from pathlib import Path
from datetime import datetime,timezone
import sympy as s
from sympy.polys.rings import ring
import json

base=Path(__file__).resolve().parent
case=json.loads((base/'rank-check-results.json').read_text())['center1_triple']
A=s.Matrix(case['A']).applyfunc(s.sympify)
B=s.Matrix(case['B']).applyfunc(s.sympify)
K=s.Matrix(case['polar_matrix']).applyfunc(s.sympify)
rt=s.sqrt(2);x,y,z=s.symbols('x y z')
cs=s.symbols('c00 c01 c02 c03 c11 c12 c13 c22 c23 c33')
sol=next(iter(s.linsolve(list(K*s.Matrix(cs))+[cs[1],cs[3]],cs)))
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('NORMALIZED_LINEAR_SOLUTION',dict(zip(cs,sol)),flush=True)
vs=sorted(set().union(*(v.free_symbols for v in sol)),key=str)
assert len(vs)==2
C=s.zeros(4);idx=0
for i in range(4):
 for j in range(i,4):C[i,j]=C[j,i]=sol[idx];idx+=1
domain=s.QQ.algebraic_field(rt)
rr,*gens=ring(','.join(map(str,[x,y,z,*vs])),domain)
M=s.ones(4)+x*A+y*B+z*C
MR=[[rr.from_expr(M[i,j]) for j in range(4)] for i in range(4)]
P=rr.zero
for mask in range(1,16):
 term=rr.one
 for i in range(4):term*=sum((MR[i][j] for j in range(4) if mask>>j&1),rr.zero)
 P+=(-1)**(4-mask.bit_count())*term
P-=24
coeff={}
for mon,c in P.items():
 key=mon[:3]
 coeff[key]=coeff.get(key,0)+domain.to_sympy(c)*s.prod(v**e for v,e in zip(vs,mon[3:]))
assert all(mon[2]>=2 for mon in coeff)
residual=list(dict.fromkeys(s.Poly(p,*vs,extension=rt).as_expr() for p in coeff.values()))
for mon,p in sorted(coeff.items()):print('COEFFICIENT',mon,s.factor(p,extension=rt),flush=True)
for p in residual:print('RESIDUAL',s.factor(p,extension=rt),flush=True)
pp,qq=vs
G1=pp**2-(6+3*rt)*pp*qq-(s.Rational(189,2)+63*rt)*qq**2
assert s.expand(coeff[(0,0,2)]-2*G1)==0
assert s.expand(coeff[(0,0,3)]-qq*(4+2*rt)*G1-(240+168*rt)*qq**3)==0
print('ELEMENTARY_CERTIFICATE cubic - (2+sqrt2)*C33*quadratic = (240+168sqrt2)*C33^3',flush=True)
GB=s.groebner(residual,*vs,extension=rt)
print('GROEBNER',list(GB),flush=True)
for v in vs:
 powers=[n for n in range(1,9) if GB.reduce(v**n)[1]==0]
 print('NILPOTENT',v,powers[0] if powers else None,flush=True)
for pivot in vs:
 other=next(v for v in vs if v!=pivot)
 chart=s.groebner([p.subs(pivot,1) for p in residual],other,extension=rt)
 print('PROJECTIVE_CHART',pivot,'basis',list(chart),flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
