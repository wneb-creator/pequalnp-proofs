import sympy as s,itertools
A,B,C,w,z=s.symbols('A B C w z')
u=s.Matrix([1,w,w*w,0]);v=s.Matrix([A+B,A+B*w,A+B*w*w,C]);T=u*v.T+v*u.T
f=s.expand(sum(s.prod(1+z*T[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
f=s.rem(f,w*w+w+1,w)
for k in range(1,5):print('coefficient',k,s.factor(f.coeff(z,k)))
print('full_permanent_delta',s.factor(f))
