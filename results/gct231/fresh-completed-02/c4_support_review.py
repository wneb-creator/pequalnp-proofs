"""Independent C4-support frame and selected exported-coefficient checks."""
from datetime import datetime,timezone
import hashlib
import itertools
import json
from pathlib import Path
import sympy as s


base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for name in ('c4_support_rational_charts.py','c4_support_charts.py','c4-support-homogeneous.json','c4-support-rational-chart-0.json'):
    print('SHA256',name,hashlib.sha256((base/name).read_bytes()).hexdigest(),flush=True)

def ryser(M):
    return s.expand(sum((-1)**(4-len(J))*s.prod(sum(M[i,j] for j in J) for i in range(4))
                        for size in range(1,5) for J in itertools.combinations(range(4),size)))

data=json.loads((base/'c4-support-homogeneous.json').read_text())
vs=s.symbols('v:7');h=s.symbols('h')
M=s.Matrix([[s.sympify(v) for v in row] for row in data['matrix']])
assert M.T==M and s.expand(sum(M))==0 and M[0,2]==M[1,3]==0
poly=s.Poly(ryser(s.ones(4)+h*M)-24,h)
assert poly.nth(0)==poly.nth(1)==0
Hs={degree:s.sympify(data['homogeneous'][str(degree)]) for degree in (2,3,4)}
assert all(s.expand(poly.nth(degree)-Hs[degree])==0 for degree in (2,3,4))
G=s.hessian(Hs[2],vs)/2
assert G.det()==-1728
print('All support homogeneous coefficients independently checked by Ryser; Gram determinant−1728',flush=True)

H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
d1,d2,d3,o1,o2,o3,b1,b2,b3=s.symbols('d1 d2 d3 o1 o2 o3 b1 b2 b3')
S=s.Matrix([[0,b1,b2,b3],[b1,d1,o3,o2],[b2,o3,d2,o1],[b3,o2,o1,d3]])
TT=H*S*H
assert s.expand(4*TT[0,2]-(-d1+d2-d3+2*b2-2*o2))==0
assert s.expand(4*TT[1,3]-(-d1+d2-d3-2*b2+2*o2))==0
u,v=s.symbols('u v');coords=[u,v,o1,o2,o3,b1,b3]
TT=TT.subs({d1:(u+v)/2,d2:u,d3:(u-v)/2,b2:o2})
vector=s.Matrix([TT[0,0],TT[1,1],TT[2,2],TT[0,1],TT[1,2],TT[2,3],TT[0,3]])
P=vector.jacobian(coords)
diag=s.diag(s.Rational(3,2),s.Rational(1,2),2,-4,2,-6,-6)
assert P.T*G*P==diag and P.det()!=0
assert M.subs(dict(zip(vs,vector)),simultaneous=True).applyfunc(s.expand)==TT.applyfunc(s.expand)
print('Support equations equivalent to d2=d1+d3 and b2=o2; coordinate determinant',P.det(),flush=True)

ee=s.Matrix.hstack(s.Matrix([2,0,0,0,0,1,0]),s.Matrix([0,0,1,1,1,0,0]),s.Matrix([0,2,1,0,-1,0,1]))
ff=s.Matrix.hstack(s.Matrix([2,0,0,0,0,-1,0])/12,s.Matrix([0,0,1,-1,1,0,0])/8,s.Matrix([0,2,1,0,-1,0,-1])/12)
zz=s.Matrix([0,4,-1,0,1,0,0])
E,F,Z=P*ee,P*ff,P*zz
target=s.BlockMatrix([[s.zeros(3),s.eye(3),s.zeros(3,1)],[s.eye(3),s.zeros(3),s.zeros(3,1)],[s.zeros(1,3),s.zeros(1,3),s.Matrix([[12]])]]).as_explicit()
frame=s.Matrix.hstack(E,F,Z)
assert frame.T*G*frame==target and frame.det()!=0
print('Rational E/F/Z frame verified; residual norm12; frame determinant',frame.det(),flush=True)

params=s.symbols('a:6');X=s.Matrix(s.symbols('x y z'))
K=s.Matrix([[0,params[0],params[1]],[-params[0],0,params[2]],[-params[1],-params[2],0]])
r=s.Matrix(1,3,params[3:]);Y=(K-6*r.T*r)*X
vectors=[]
for chart in range(8):
    left=s.Matrix([Y[i] if chart>>i&1 else X[i] for i in range(3)])
    right=s.Matrix([X[i] if chart>>i&1 else Y[i] for i in range(3)])
    vector=E*left+F*right+Z*(r*X)[0]
    assert s.expand((vector.T*G*vector)[0])==0
    vectors.append(vector)
print('All8 six-parameter chart graph identities checked',flush=True)

export=json.loads((base/'c4-support-rational-chart-0.json').read_text())
assert export['parameters']==list(map(str,params)) and len(export['equations'])==25
eq=[s.sympify(p) for p in export['equations']]
monomials=[]
for degree in (3,4):
    monomials.extend(sorted([m for m in itertools.product(range(degree+1),repeat=3) if sum(m)==degree],reverse=True))
ratios={}
for number,values in enumerate([[0]*6,[1]*6,[-2,-1,0,1,2,3],[2,-3,1,0,-1,2]]):
    sample=dict(zip(params,values))
    vv=vectors[0].subs(sample)
    perturb=M.subs(dict(zip(vs,vv)),simultaneous=True)
    pp=s.Poly(ryser(s.ones(4)+perturb)-24,*X)
    assert all(sum(mon)>=3 for mon,coefficient in pp.terms() if coefficient)
    for index,(expression,monomial) in enumerate(zip(eq,monomials)):
        emitted=s.expand(expression.subs(sample))
        actual=pp.coeff_monomial(monomial)
        if emitted==0:assert actual==0
        else:
            ratio=actual/emitted
            assert ratio!=0
            if index in ratios:assert ratio==ratios[index]
            else:ratios[index]=ratio
    print('Chart0 independent exact Ryser sample',number,'passed',flush=True)
assert len(ratios)==25
print('All25 exported coefficients agree up to fixed nonzero denominator-clearing factors',flush=True)
print('No Groebner basis run or chart solution verdict is part of this review',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
