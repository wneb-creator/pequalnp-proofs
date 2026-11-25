import sympy as s
from itertools import permutations
x,y,z=s.symbols('x y z')
r=s.sqrt(2)
b=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4); k=0
for i in range(4):
 for j in range(i,4): B[i,j]=B[j,i]=b[k]; k+=1
A=s.Matrix([[r-1,1],[1,-r-1]])
T=s.diag(x*A,y*A)
M=s.ones(4)+T+z*B
f=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in permutations(range(4)))-24),z)
assert f.coeff_monomial(1)==0
lin=s.Poly(f.coeff_monomial(z),x,y)
sol=s.linsolve(lin.coeffs()+[b[1],b[8]],b)
print('linear solutions',sol,flush=True)
sub=dict(zip(b,next(iter(sol))))
rest=s.expand(f.as_expr().subs(sub))
cs=[s.factor(c,extension=r) for c in s.Poly(rest,x,y,z).coeffs()]
cs=list(dict.fromkeys(c for c in cs if c!=0))
print('constraints',cs,flush=True)
vs=sorted(set().union(*(c.free_symbols for c in cs)),key=str)
print('remaining symbols',vs,flush=True)
g=s.groebner(cs,*vs,extension=r,order='grevlex')
print('groebner',list(g),flush=True)
for v in vs:
 power=next((n for n in range(1,17) if g.reduce(v**n)[1]==0),None)
 assert power is not None
 print('nilpotent certificate',v,power,flush=True)
print('linear sub',sub,flush=True)
