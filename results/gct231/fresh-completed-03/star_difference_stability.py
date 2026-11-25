import sympy as s,itertools
x,y=s.symbols('x y');bb=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4);k=0
for i in range(4):
 for j in range(i,4):B[i,j]=B[j,i]=bb[k];k+=1
A=s.Matrix([[0,1,-1,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0]])
M=s.ones(4)+x*A+y*B
P=s.Poly(s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),x,y)
lin=[v for mon,v in P.terms() if mon[1]==1]+[bb[1]]
sol=next(iter(s.linsolve(lin,bb)));sub=dict(zip(bb,sol))
print('linear',sub,flush=True)
mixed=s.factor(P.coeff_monomial(x*x*y*y).subs(sub))
assert mixed==(bb[6]-bb[8])**2
print('mixed coefficient',mixed,flush=True)
T=B.subs(sub).subs(bb[6],bb[8])
even=T+T[0,2]*A/2
perm=[0,2,1,3]
assert even==s.Matrix(4,4,lambda i,j:even[perm[i],perm[j]])
assert -A==s.Matrix(4,4,lambda i,j:A[perm[i],perm[j]])
print('T plus T02/2 A is invariant under (1 2); A is anti-invariant',flush=True)
print('ALL_CHECKS_PASSED',flush=True)
