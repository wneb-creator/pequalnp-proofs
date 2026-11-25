import sympy as s,itertools
x,y,z=s.symbols('x y z'); rt=s.sqrt(2)
coords=[(i,j) for i in range(4) for j in range(i,4)]
c=s.symbols('c0:10'); C=s.zeros(4)
for (i,j),a in zip(coords,c): C[i,j]=C[j,i]=a
A=s.zeros(4); B=s.zeros(4)
for M,off in [(A,0),(B,2)]:
 M[off,off]=rt-1; M[off,off+1]=M[off+1,off]=1; M[off+1,off+1]=-rt-1
M=s.ones(4)+x*A+y*B
D=s.expand(sum(sum(C[i,pi[i]]*s.prod(M[j,pi[j]] for j in range(4) if j!=i) for i in range(4)) for pi in itertools.permutations(range(4))))
eq=s.Poly(D,x,y).coeffs()+[c[0],c[7]]; E=s.linear_eq_to_matrix(eq,c)[0]
ns=[v.applyfunc(s.simplify) for v in E.nullspace()]; print('nullspace',ns,flush=True)
p=s.symbols('p:'+str(len(ns))); sol=sum((a*v for a,v in zip(p,ns)),s.zeros(10,1)); Ct=C.subs(dict(zip(c,sol)))
print('C',Ct,flush=True)
N=M+z*Ct
P=s.expand(sum(s.prod(N[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4))))
polys=[s.factor(s.simplify(v)) for k,v in s.Poly(P-24,x,y,z).terms() if k[2]>=2]
print('equations',polys,flush=True)
G=s.groebner(polys,*p,extension=rt)
print('groebner',G,flush=True)
print('zero_dim',G.is_zero_dimensional,flush=True)
print('solutions',s.solve(polys,p),flush=True)
