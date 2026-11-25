import sympy as s
from itertools import permutations,product
import time
u,d,h,i,j,z=s.symbols('u d h i j z');X=s.Matrix([u,d,h,i,j]);vs=list(X)
a=-2*u-2*d-4*h-4*i-j
B=s.Matrix([[a,u,0,d],[u,h,h,i],[0,h,h,i],[d,i,i,j]])
M=s.ones(4)+z*B
P=s.Poly(s.expand(sum(s.prod(M[k,l] for k,l in enumerate(q)) for q in permutations(range(4)))-24),z)
polys={k:s.expand(P.coeff_monomial(z**k)) for k in [2,3,4]}
Q=s.hessian(polys[2],X)/4
E=s.Matrix.hstack(s.Matrix([1,-1,0,0,0]),s.Matrix([0,1,1,-1,3]))
W=E.T*Q
F=[]
for k in range(2):
 sol=next(iter(s.linsolve((W,s.eye(2)[:,k]))))
 free=set().union(*(x.free_symbols for x in sol));F.append(s.Matrix(sol).subs(dict.fromkeys(free,0)))
F=s.Matrix.hstack(*F);F=F-E*(F.T*Q*F)/2
v=(E.row_join(F).T*Q).nullspace()[0];v=v/s.sqrt((v.T*Q*v)[0])
print('E',E,'F',F,'v',v,sep='\n',flush=True)
print('Gram',E.row_join(F).row_join(v).T*Q*E.row_join(F).row_join(v),flush=True)
a,b,c,x,y=s.symbols('a b c x y');start=time.time()
for swaps in product([False,True],repeat=2):
 EE=s.Matrix.hstack(*(F[:,k] if swaps[k] else E[:,k] for k in range(2)))
 FF=s.Matrix.hstack(*(E[:,k] if swaps[k] else F[:,k] for k in range(2)))
 U1=EE[:,0]-b*b*FF[:,0]/2+(-a-b*c/2)*FF[:,1]+b*v
 U2=EE[:,1]+(a-b*c/2)*FF[:,0]-c*c*FF[:,1]/2+c*v
 sub=dict(zip(vs,U1*x+U2*y))
 assert s.expand(polys[2].subs(sub,simultaneous=True))==0
 equations=[]
 for k in [3,4]:
  expr=s.Poly(s.expand(polys[k].subs(sub,simultaneous=True)),x,y)
  equations.extend(expr.coeffs())
 eq=[s.Poly(f,a,b,c).clear_denoms()[1].as_expr() for f in equations]
 print('chart',swaps,'equations',len(eq),'start',time.time()-start,flush=True)
 g=s.groebner(eq,a,b,c,order='grevlex');print('GB',g,'elapsed',time.time()-start,flush=True)
 if len(g.polys)!=1 or g.polys[0].as_expr()!=1:
  print('LEX',s.groebner(eq,a,b,c,order='lex'),flush=True)
