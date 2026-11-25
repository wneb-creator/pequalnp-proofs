import sympy as s
from itertools import permutations
u,v,q,w,h=s.symbols('u v q w h')
B=s.Matrix([[0,u,u*w,u*w*w],[u,v,q,q*w*w],[u*w,q,v*w,q*w],[u*w*w,q*w*w,q*w,v*w*w]])
M=s.ones(4)+h*B
f=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in permutations(range(4)))-24),h)
for k in range(1,5):print(k,s.factor(s.rem(f.coeff_monomial(h**k),w*w+w+1,w)))
