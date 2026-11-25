import sympy as s
from datetime import datetime,timezone
print(datetime.now(timezone.utc).isoformat(),flush=True)
a,b,c=s.symbols('a b c'); x,y,z=s.symbols('x y z'); v=s.Matrix([x,y,z]); alpha=s.sqrt(2)*s.I
K=s.Matrix([[0,a,b],[-a,0,c],[-b,-c,0]])
d=(s.eye(3)+K)*v; o=s.diag(-1,1,1)*alpha/2*(s.eye(3)-K)*v
B=s.Matrix([[d[0],o[2],o[1]],[o[2],d[1],o[0]],[o[1],o[0],d[2]]])
f=s.expand(d[0]*d[1]*d[2]+d[0]*o[0]**2+d[1]*o[1]**2+d[2]*o[2]**2+2*o[0]*o[1]*o[2])
cs=s.Poly(f,x,y,z).coeffs()
for mon,coef in s.Poly(f,x,y,z).terms(): print(mon,s.factor(coef),flush=True)
print('Groebner start',flush=True)
g=s.groebner(cs,a,b,c,extension=alpha,order='grevlex')
print('Groebner',g,flush=True)
print(datetime.now(timezone.utc).isoformat(),flush=True)
