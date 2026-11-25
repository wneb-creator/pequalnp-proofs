from pathlib import Path
from datetime import datetime,timezone
import hashlib,itertools
import sympy as s
root=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Lean source SHA256',hashlib.sha256((root/'IsolatedVertex.lean').read_bytes()).hexdigest(),flush=True)
d,a,b,c,e,f,g,z=s.symbols('d a b c e f g z')
M=s.Matrix([[d,0,0,0],[0,a,b,c],[0,b,e,f],[0,c,f,g]])
sm=a+e+g+2*b+2*c+2*f
r=a*e+a*g+e*g+b**2+c**2+f**2+2*(a*f+b*c+b*f+c*e+b*g+c*f)
p=a*e*g+2*b*c*f+a*f**2+e*c**2+g*b**2
L=6*(sm+d);Q=2*(r+sm*d);C=p+d*r;F=d*p
ryser=0
for mask in range(1,16):
 rows=[sum(1+z*M[i,j] for j in range(4) if mask>>j&1) for i in range(4)]
 ryser+=(-1)**(4-mask.bit_count())*s.prod(rows)
assert s.expand(ryser-(24+L*z+Q*z**2+C*z**3+F*z**4))==0
assert s.expand(d**4-(-F+d*C-d**2*Q/2+d**3*L/6))==0
l,q,cc,ff=s.symbols('L Q C F');v=l*z+q*z**2+cc*z**3+ff*z**4
vals=[v.subs(z,t) for t in (1,-1,2,-2)]
weights=[[s.Rational(2,3),-s.Rational(2,3),-s.Rational(1,12),s.Rational(1,12)],[s.Rational(2,3),s.Rational(2,3),-s.Rational(1,24),-s.Rational(1,24)],[-s.Rational(1,6),s.Rational(1,6),s.Rational(1,12),-s.Rational(1,12)],[-s.Rational(1,6),-s.Rational(1,6),s.Rational(1,24),s.Rational(1,24)]]
for ws,want in zip(weights,(l,q,cc,ff)):
 assert s.expand(sum(x*y for x,y in zip(ws,vals))-want)==0
print('Ryser expansion, all four evaluation weights, and d^4 certificate: PASS',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
