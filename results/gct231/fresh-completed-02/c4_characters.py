import sympy as s,itertools
vs=s.symbols('a:10');M=s.zeros(4);idx=0
for i in range(4):
 for j in range(i,4):M[i,j]=M[j,i]=vs[idx];idx+=1
rho=s.Matrix(4,4,lambda i,j:M[(i+1)%4,(j+1)%4])
h=s.symbols('h')
for char in [1,-1,s.I,-s.I]:
 eq=list(rho-char*M)
 if char==1:eq.append(sum(M))
 sol=next(iter(s.linsolve(eq,vs)));T=M.subs(dict(zip(vs,sol)))
 params=sorted(set().union(*(v.free_symbols for v in sol)),key=str)
 A=s.ones(4)+h*T
 P=s.Poly(s.expand(sum(s.prod(A[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),h)
 print('CHAR',char,'params',params,'matrix',T,flush=True)
 print('coefficients',[s.factor(P.nth(k)) for k in [1,2,3,4]],flush=True)
