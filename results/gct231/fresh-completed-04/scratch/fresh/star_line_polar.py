import sympy as s,itertools
t,x,y=s.symbols('t x y');bb=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4);k=0
for i in range(4):
 for j in range(i,4):B[i,j]=B[j,i]=bb[k];k+=1
A=s.Matrix([[0,1,t,-1-t],[1,0,0,0],[t,0,0,0],[-1-t,0,0,0]])
M=s.ones(4)+x*A+y*B
P=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),x,y)
linear=[q for mon,q in P.terms() if mon[1]==1]+[bb[1]]
sol=next(iter(s.linsolve(linear,bb)));sub=dict(zip(bb,sol))
print('LINEAR',sub,flush=True)
quart=s.factor(P.coeff_monomial(x*x*y*y).subs(sub));print('MIXED_QUARTIC',quart,flush=True)
vs=sorted(set().union(*(q.free_symbols for q in sol))-{t},key=str)
Q=s.hessian(quart,vs)/2
print('FREE',vs,'QUARTIC_HESSIAN_RANK',Q.rank(),flush=True)
print('QUARTIC_HESSIAN',Q,flush=True)
