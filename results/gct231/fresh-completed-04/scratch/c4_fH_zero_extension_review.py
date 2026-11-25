from pathlib import Path
from datetime import datetime,timezone
import json
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
F,J,z,t=s.symbols('F J z t')
data=json.loads((base/'c4_factor_coordinates.json').read_text())
q=s.sympify(data['Q4']);c=s.sympify(data['C16'])
vs=(a,b,X,Y)
qW=s.expand(q.subs({e:0,f:0,H:0}))
G=s.hessian(qW,vs)/2
assert G.det()==s.Rational(9,4)
wsub={e:1,f:F,H:J,a:0,b:0,X:0,Y:0}
assert s.expand(q.subs(wsub)-(6+2*F**2-J**2))==0
assert s.expand(c.subs(wsub)-4*(F**2-1))==0
c_line=s.Poly(s.expand(c.subs({e:z,f:F*z,H:J*z})),z)
R=c_line.nth(1)
expected=2*F*a*b-2*J*X*Y-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a**2-b**2
assert s.expand(R-expected)==0 and c_line.nth(2)==0
B=s.hessian(R,vs)/2
D=s.factor((B-t*G).det())
reduced=s.rem(s.rem(D,F**2-1,F),J**2-8,J)
target=t**2*(9*t**2+12*t+16)/4
assert s.expand(reduced-target)==0
assert s.discriminant(9*t*t+12*t+16,t)==-432
assert s.degree(s.gcd(s.Poly(target,t),s.Poly(s.diff(target,t),t)))==1
print('q(w)=',s.expand(q.subs(wsub)),'c(w)=',s.expand(c.subs(wsub)),flush=True)
print('Mixed quadratic R=',R,flush=True)
print('General determinant=',D,flush=True)
print('Under F^2=1,J^2=8 determinant=',target,flush=True)
print('Remaining quadratic discriminant=-432; determinant is not a square over C',flush=True)
aa,bb,cc,dd,ee,ff,gg=s.symbols('A B C D E F G')
block=s.Matrix([[0,0,aa,bb],[0,0,cc,dd],[aa,cc,ee,ff],[bb,dd,ff,gg]])
assert s.expand(block.det()-(aa*dd-bb*cc)**2)==0
print('Common isotropic2-plane block determinant identity: PASS',flush=True)
print('No Q+C extension of a2-plane K in e=f=H=0 to e=1',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
