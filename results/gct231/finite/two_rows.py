import sympy as s,itertools,json
from pathlib import Path
a,b,c,x,y,z,w,q=s.symbols('a b c x y z w q')
T=s.Matrix([[a,b,x,y],[b,c,z,w],[x,z,0,0],[y,w,0,0]])
f=s.expand(sum(s.prod(1+q*T[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4)))-24)
for d in range(1,5):print('degree',d,s.factor(f.coeff(q,d)))
u,v,k=s.symbols('u v k')
f=s.expand(f.subs({x:u,y:v,z:k*u,w:-k*v}))
for d in range(1,5):print('ruling_degree',d,s.factor(f.coeff(q,d)))
