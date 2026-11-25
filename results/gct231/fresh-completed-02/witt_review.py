"""Independent exact checks; does not expand the dense twelve-variable permanent."""
from datetime import datetime,timezone
import hashlib
import itertools
import json
from math import gcd,prod
from pathlib import Path
import random
import sympy as s


base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for name in ('witt_hadamard.py','witt_lifted.py','witt-hadamard-frame.json','witt-lifted-equations.json'):
    print('SHA256',name,hashlib.sha256((base/name).read_bytes()).hexdigest(),flush=True)
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
assert H.T==H and H*H==s.eye(4)
coords=s.symbols('d0:3 o0:3 b0:3')
d0,d1,d2,o0,o1,o2,b0,b1,b2=coords
M=s.Matrix([[0,b0,b1,b2],[b0,d0,o2,o1],[b1,o2,d1,o0],[b2,o1,o0,d2]])
T=H*M*H
assert sum(T)==0 and T.T==T
raw=[T.diff(v) for v in coords]
assert s.Matrix.hstack(*[s.Matrix(list(m)) for m in raw]).rank()==9
H2=s.expand(sum(T[i,p[i]]*T[j,p[j]] for p in itertools.permutations(range(4))
              for i,j in itertools.combinations(range(4),2)))
G=s.diag(1,1,1,2,2,2,-6,-6,-6)
assert H2==(s.Matrix(coords).T*G*s.Matrix(coords))[0].expand()
print('Hadamard tangent basis is symmetric, tangent, independent; degree-two coefficient independently checked',flush=True)

E=s.Matrix.vstack(2*s.eye(3),s.eye(3),s.eye(3))
F=s.Matrix.vstack(2*s.eye(3),s.eye(3),-s.eye(3))/12
R=s.Matrix.vstack(s.eye(3),-s.eye(3),s.zeros(3))
frame=s.Matrix.hstack(E,F,R)
expected=s.BlockMatrix([[s.zeros(3),s.eye(3),s.zeros(3)],[s.eye(3),s.zeros(3),s.zeros(3)],[s.zeros(3),s.zeros(3),3*s.eye(3)]]).as_explicit()
assert frame.T*G*frame==expected and frame.det()!=0
saved=json.loads((base/'witt-hadamard-frame.json').read_text())
assert all(s.Matrix(4,4,[s.Rational(v) for v in row])==m for row,m in zip(saved['tangent_basis'],raw))
for label,actual in [('E',E),('F',F),('R',R),('D',3*s.eye(3))]:
    assert s.Matrix([[s.Rational(v) for v in row] for row in saved[label]])==actual
print('Rational frame and exported frame JSON checked; determinant',frame.det(),flush=True)

aa=s.symbols('a:18')
K=s.Matrix([[0,aa[0],aa[1]],[-aa[0],0,aa[2]],[-aa[1],-aa[2],0]])
Z=s.Matrix(3,3,aa[3:12])
S=s.Matrix([[aa[12],aa[13],aa[14]],[aa[13],aa[15],aa[16]],[aa[14],aa[16],aa[17]]])
C=E+F*(K-s.Rational(3,2)*Z.T*Z)+R*Z
assert (C.T*G*C).applyfunc(s.expand)==s.zeros(3)
lift=E+F*(K+S)+R*Z
assert (lift.T*G*lift-(2*S+3*Z.T*Z)).applyfunc(s.expand)==s.zeros(3)
BB=s.Matrix(3,3,s.symbols('B:9'))
general=E+F*BB+R*Z
assert (general.T*G*general-(BB+BB.T+3*Z.T*Z)).applyfunc(s.expand)==s.zeros(3)
print('General graph Gram equation, isotropic graph formula, and lifted Gram equation checked',flush=True)

EE=s.Matrix.hstack(E,R[:,0]+s.I*R[:,1])
FF=s.Matrix.hstack(F,(R[:,0]-s.I*R[:,1])/6)
rr=R[:,2]
full=s.Matrix.hstack(EE,FF,rr)
gg=s.BlockMatrix([[s.zeros(4),s.eye(4),s.zeros(4,1)],[s.eye(4),s.zeros(4),s.zeros(4,1)],[s.zeros(1,4),s.zeros(1,4),s.Matrix([[3]])]]).as_explicit()
assert (full.T*G*full).applyfunc(s.expand)==gg
residual=s.Matrix([[0,1,0],[1,0,0],[0,0,3]])
target=s.BlockMatrix([[s.zeros(3),s.eye(3),s.zeros(3)],[s.eye(3),s.zeros(3),s.zeros(3)],[s.zeros(3),s.zeros(3),residual]]).as_explicit()
charts=0
for omitted in range(4):
    chosen=[i for i in range(4) if i!=omitted]
    for bits in range(8):
        left=s.Matrix.hstack(*[(FF if bits>>j&1 else EE)[:,i] for j,i in enumerate(chosen)])
        right=s.Matrix.hstack(*[(EE if bits>>j&1 else FF)[:,i] for j,i in enumerate(chosen)])
        rem=s.Matrix.hstack(EE[:,omitted],FF[:,omitted],rr)
        cc=s.Matrix.hstack(left,right,rem)
        assert (cc.T*G*cc).applyfunc(s.expand)==target
        charts+=1
assert charts==32 and target.det()!=0
print('All32 complete-chart frames checked with residual Gram',list(residual),flush=True)

data=json.loads((base/'witt-lifted-equations.json').read_text())
assert data['parameters']==[str(a) for a in aa]
equations={}
for eq in data['equations']:
    key=tuple(eq['monomial'])
    assert sum(key)==eq['degree'] and key not in equations
    terms=[];content=0
    for coefficient,exponents in eq['terms']:
        coefficient=int(coefficient)
        assert len(exponents)==18 and all(isinstance(v,int) and v>=0 for v in exponents)
        assert sum(exponents)<=eq['degree']
        terms.append((coefficient,[(j,p) for j,p in enumerate(exponents) if p]))
        content=gcd(content,abs(coefficient))
    assert content==1
    equations[key]=terms
assert len(equations)==31

def ryser(matrix):
    return s.expand(sum((-1)**(4-len(J))*s.prod(sum(matrix[i,j] for j in J) for i in range(4))
                        for size in range(1,5) for J in itertools.combinations(range(4),size)))

x=s.Matrix(s.symbols('x y z'))
samples=[[0]*18,[1]*18,[(j%5)-2 for j in range(18)]]
rng=random.Random(231)
samples.extend([[rng.randrange(-3,4) for _ in range(18)] for _ in range(3)])
scales={}
for number,values in enumerate(samples):
    numeric=lift.subs(dict(zip(aa,values)))
    perturb=s.zeros(4)
    for value,basis in zip(numeric*x,raw):perturb+=value*basis
    poly=s.Poly(ryser(s.ones(4)+perturb)-24,*x)
    assert all(sum(mon)>=2 for mon,coef in poly.terms() if coef)
    for mon,terms in equations.items():
        exported=sum(c*prod(values[j]**power for j,power in powers) for c,powers in terms)
        actual=poly.coeff_monomial(mon)
        if exported==0:
            assert actual==0,(number,mon)
        else:
            ratio=actual/exported
            assert ratio!=0
            if mon in scales:assert scales[mon]==ratio,(number,mon)
            else:scales[mon]=ratio
    print('Selected exact lifted Ryser check',number,'passed',flush=True)
assert len(scales)==31
print('All31 primitive export coefficients match fixed nonzero rational scales across six exact samples',flush=True)
print('Export scaling factors',[(mon,str(scales[mon])) for mon in sorted(scales)],flush=True)
print('No dense twelve-variable permanent expansion rerun; no chart ideal solved',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
