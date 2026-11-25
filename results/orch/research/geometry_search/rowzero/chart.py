import sympy as S
from pathlib import Path

p = S.symbols('p0:3')
r,s,t = S.symbols('r s t')
k = S.sqrt(2)*S.I
A = S.Matrix([[0,r,s],[-r,0,t],[-s,-t,0]])
P = S.Matrix(p)
Q = A*P
diag = (P+Q)/2
off = (P-Q)/(2*k)
x,y,z=diag
a,b,c=off
f=S.expand(x*y*z+a*a*z+b*b*y+c*c*x+2*a*b*c)
coeffs=[S.simplify(v*8) for v in S.Poly(f,*p).coeffs()]
print('coefficients',len(coeffs),flush=True)
for v in coeffs:print(v,flush=True)
G=S.groebner(coeffs,r,s,t,extension=k)
print('Groebner',G,flush=True)
for g in G.polys:print(g.as_expr(),flush=True)
print('solutions',S.solve_poly_system([g.as_expr() for g in G.polys],r,s,t),flush=True)
