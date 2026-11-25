"""Independent C4 character and opposite-character pair checks by Ryser."""
from datetime import datetime,timezone
import hashlib
import itertools
from pathlib import Path
import sympy as s


base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for filename in ('c4_characters.py','c4_planes.py'):
    print('SHA256',filename,hashlib.sha256((base/filename).read_bytes()).hexdigest(),flush=True)

def ryser(M):
    return s.expand(sum((-1)**(4-len(J))*s.prod(sum(M[i,j] for j in J) for i in range(4))
                        for size in range(1,5) for J in itertools.combinations(range(4),size)))

u,v,a,b,c,h,y,z=s.symbols('u v a b c h y z')
fixed=s.Matrix([[v,u,-2*u-v,u],[u,v,u,-2*u-v],[-2*u-v,u,v,u],[u,-2*u-v,u,v]])
minus=s.Matrix([[-c,b,-a,-b],[b,c,-b,a],[-a,-b,-c,b],[-b,a,b,c]])
def charmat(u,v,sign):
    j=sign*s.I
    return s.Matrix([[j*v,-u,0,j*u],[-u,-v,-j*u,0],[0,-j*u,-j*v,u],[j*u,0,u,v]])

for eigenvalue,T in [(1,fixed),(-1,minus),(s.I,charmat(u,v,1)),(-s.I,charmat(u,v,-1))]:
    assert T.T==T and s.expand(sum(T))==0
    assert all(s.expand(T[(i+1)%4,(j+1)%4]-eigenvalue*T[i,j])==0 for i in range(4) for j in range(4))
    poly=s.Poly(ryser(s.ones(4)+h*T)-24,h)
    print('Character',eigenvalue,'Ryser coefficients',[s.factor(poly.nth(k)) for k in range(1,5)],flush=True)
    if eigenvalue==1:
        assert s.expand(poly.nth(2)-8*(3*u*u+2*u*v+v*v))==0
        assert s.expand(poly.nth(3)+16*u*(u+v)**2)==0
    elif eigenvalue==-1:
        assert s.expand(poly.nth(2)+4*(a*a+4*a*c-2*b*b+c*c))==0
        assert s.det(s.hessian(poly.nth(2),[a,b,c])/2)==-384
    else:
        assert all(poly.nth(k)==0 for k in (1,2,3))
        sign=1 if eigenvalue==s.I else -1
        assert s.expand(poly.nth(4)+sign*s.I*v*v*(4*u*u-sign*s.I*v*v))==0

pairs=[(i,j) for i in range(4) for j in range(i,4)]
action=s.zeros(10)
for row,(i,j) in enumerate(pairs):action[row,pairs.index(tuple(sorted(((i+1)%4,(j+1)%4))))]=1
t=s.symbols('t')
assert s.factor(action.charpoly(t).as_expr())==(t-1)**3*(t+1)**3*(t*t+1)**2
print('Full symmetric character multiplicities are3,3,2,2; tangent multiplicities2,3,2,2',flush=True)

up=[(1,0)]+[(sgn*(1+s.I)/(2*s.sqrt(2)),1) for sgn in (1,-1)]
down=[(1,0)]+[(sgn*(1-s.I)/(2*s.sqrt(2)),1) for sgn in (1,-1)]
for i,uv in enumerate(up):
    for j,st in enumerate(down):
        U=charmat(*uv,1);V=charmat(*st,-1)
        assert s.expand(ryser(s.ones(4)+y*U)-24)==0
        assert s.expand(ryser(s.ones(4)+z*V)-24)==0
        poly=s.Poly(ryser(s.ones(4)+y*U+z*V)-24,y,z,extension=s.I+s.sqrt(2))
        assert not poly.is_zero
        monomial,coefficient=poly.terms()[0]
        assert coefficient!=0
        print('Opposite-character pair',i,j,'nonzero coefficient',monomial,s.simplify(coefficient),flush=True)
print('All nine opposite-character pairs fail; no C4-stable solution3-plane',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
