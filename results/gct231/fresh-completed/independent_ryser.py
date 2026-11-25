"""Independent exact permanent checks for the C3 and block-seed reviews."""
import contextlib
import io
import itertools
from pathlib import Path
import runpy
import time
import sympy as s


def ryser(M):
    return s.expand(sum((-1)**(4-len(S))*s.prod(sum(M[i,j] for j in S) for i in range(4))
                        for k in range(1,5) for S in itertools.combinations(range(4),k)))


begin=time.monotonic()
b,c,d,u,v,q,w,h=s.symbols('b c d u v q w h')
A=s.Matrix([[-6*b-3*c-6*d,b,b,b],[b,c,d,d],[b,d,c,d],[b,d,d,c]])
C2=-6*(-3*b*b+2*b*c+4*b*d+2*c*c+10*c*d+9*d*d)
C3=-4*(-3*b*b*c-6*b*b*d+3*b*c*c+6*b*c*d+9*b*d*d+2*c**3+9*c*c*d+15*c*d*d+13*d**3)
C4=-3*(-b*b*c*c-2*b*b*c*d-3*b*b*d*d+2*b*c**3+6*b*c*d*d+4*b*d**3+c**4+2*c**3*d+3*c*c*d*d+8*c*d**3+4*d**4)
assert s.expand(ryser(s.ones(4)+h*A)-24-C2*h*h-C3*h**3-C4*h**4)==0
print('C3 invariant coefficients independently checked by Ryser',flush=True)

B=s.Matrix([[0,u,u*w,u*w*w],[u,v,q,q*w*w],[u*w,q,v*w,q*w],[u*w*w,q*w*w,q*w,v*w*w]])
F=2*q**3-3*q*q*v*(w+1)+6*q*u*u*w-6*q*u*v*w+3*u*u*v+6*u*v*v+v**3
def red(f):return s.rem(s.expand(f),w*w+w+1,w)
assert red(ryser(s.ones(4)+h*B)-24-h**3*F)==0
sigma=[0,2,3,1]
assert all(red(B[sigma[i],sigma[j]]-w*B[i,j])==0 for i in range(4) for j in range(4))
print('C3 character permanent identity and eigenmatrix equation independently checked',flush=True)
pairs=list(itertools.combinations(range(4),2))+[(i,i) for i in range(4)]
P=s.zeros(10)
for row,(i,j) in enumerate(pairs):P[row,pairs.index(tuple(sorted((sigma[i],sigma[j]))))]=1
z=s.symbols('z')
print('C3 symmetric representation characteristic polynomial',s.factor(P.charpoly(z).as_expr()),flush=True)

path=Path(__file__).resolve().parent/'block_seed'/'extend.py'
with contextlib.redirect_stdout(io.StringIO()):data=runpy.run_path(str(path))
assert s.expand(ryser(data['M'])-24-data['f'].as_expr())==0
linear=s.Poly(data['f'].coeff_monomial(data['z']),data['x'],data['y'])
assert all(s.simplify(e.subs(data['sub']))==0 for e in linear.coeffs())
assert data['B'].subs(data['sub']).subs({v:0 for v in data['vs']})==s.zeros(4)
print('Block seed full polynomial independently checked by Ryser',flush=True)
print('Block seed linear substitution annihilates every linear coefficient',flush=True)
print('Block seed residual variables',data['vs'],flush=True)
powers=[(str(v),next(n for n in range(1,17) if data['g'].reduce(v**n)[1]==0)) for v in data['vs']]
print('Block seed verified vanishing power remainders',powers,flush=True)
print('Block seed residual origin makes every normalized B entry zero',flush=True)
print('All independent checks passed; elapsed seconds',time.monotonic()-begin,flush=True)
