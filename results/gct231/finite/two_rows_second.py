import sympy as s,itertools
a,b,c,u,v,k,z=s.symbols('a b c u v k z')
T=s.Matrix([[a,b,u,k*u],[b,c,v,-k*v],[u,v,0,0],[k*u,-k*v,0,0]])
f=s.expand(sum(s.prod(1+z*T[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
for d in range(1,5):print('coefficient',d,s.factor(f.coeff(z,d)))
