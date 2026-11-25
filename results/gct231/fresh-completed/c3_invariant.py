import sympy as s,itertools
b,c,d,t=s.symbols('b c d t');a=-6*b-3*c-6*d
A=s.Matrix([[a,b,b,b],[b,c,d,d],[b,d,c,d],[b,d,d,c]])
M=s.ones(4)+t*A
f=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),t)
eq=[s.factor(f.coeff_monomial(t**k)) for k in [2,3,4]]
for e in eq:print(e)
g=s.groebner(eq,b,c,d,order='grevlex');print(g)
print('basis factored')
for e in g.polys:print(s.factor(e.as_expr()))
print('b1',s.groebner([e.subs(b,1) for e in eq],c,d,order='lex'))
print('b0d1',s.groebner([e.subs({b:0,d:1}) for e in eq],c,order='lex'))
