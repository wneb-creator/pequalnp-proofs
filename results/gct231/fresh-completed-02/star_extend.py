import sympy as s
from itertools import permutations
x,y,z=s.symbols('x y z')
b=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4); k=0
for i in range(4):
 for j in range(i,4): B[i,j]=B[j,i]=b[k]; k+=1
T=s.Matrix([[0,x,y,-x-y],[x,0,0,0],[y,0,0,0],[-x-y,0,0,0]])
M=s.ones(4)+T+z*B
f=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in permutations(range(4)))-24),z)
lin=s.Poly(f.coeff_monomial(z),x,y)
sol=s.linsolve(lin.coeffs(),b)
print('linear solutions',sol)
sub=dict(zip(b,next(iter(sol))))
rest=s.expand(f.as_expr().subs(sub))
print('residual',s.factor(rest))
print('constraints', [s.factor(c) for c in s.Poly(rest,x,y,z).coeffs()])
