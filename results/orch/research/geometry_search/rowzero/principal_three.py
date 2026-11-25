import sympy as S,itertools,time,json,sys,signal
from pathlib import Path

a,b,d,e,f=S.symbols('a b d e f');vs=(a,b,d,e,f)
c=-a-b-2*d-2*e-2*f
M=S.Matrix([[a,d,e],[d,b,f],[e,f,c]])
Q=S.expand(S.trace(M*M)-2*sum(sum(M[i,j] for j in range(3))**2 for i in range(3)))
C=S.expand(a*b*c+a*f*f+b*e*e+c*d*d+2*d*e*f)
G=S.hessian(Q,vs)/2
X=S.Matrix([[0,0],[0,0],[1,0],[-1,-1],[0,1]])
R=S.Matrix([[1,0],[0,1],[0,0],[0,0],[0,0]])
U=X.T*G*R
Y0=R*U.inv()/2
Y=Y0-X*(Y0.T*G*Y0)
Z=S.Matrix.vstack(X.T*G,Y.T*G).nullspace()[0]
P=S.Matrix.hstack(X,Y,Z)
print('Q',Q,flush=True);print('GRAM',G,flush=True);print('WITT',P,flush=True)
print('WITT GRAM',P.T*G*P,flush=True)
x1,x2,y1,y2,z=S.symbols('x1 x2 y1 y2 z');cs=S.Matrix([x1,x2,y1,y2,z])
kappa=(Z.T*G*Z)[0]
q=S.expand(Q.subs(dict(zip(vs,P*cs))))
assert S.expand(q-x1*y1-x2*y2-kappa*z*z)==0
cubic=S.expand(C.subs(dict(zip(vs,P*cs))))
A,B,K,s,t=S.symbols('A B K s t')
zz=A*s+B*t;yy1=-kappa*A*zz+K*t;yy2=-kappa*B*zz-K*s
for flip in itertools.product([0,1],repeat=2):
 print('CHART',flip,'START',time.time(),flush=True)
 sub={x1:yy1 if flip[0] else s,y1:s if flip[0] else yy1,x2:yy2 if flip[1] else t,y2:t if flip[1] else yy2,z:zz}
 eq=[]
 for co in S.Poly(S.expand(cubic.subs(sub)),s,t).coeffs():
  eq.append(S.Poly(co,A,B,K).clear_denoms()[1].primitive()[1].as_expr())
 for co in eq:print('COEFFICIENT',S.factor(co),flush=True)
 modulus=int(sys.argv[1]) if len(sys.argv)>1 else None
 if modulus:signal.alarm(45)
 Gc=S.groebner(eq,A,B,K,order='grevlex',method='f5b',modulus=modulus)
 if modulus:signal.alarm(0)
 print('GROEBNER',Gc,flush=True)
 if list(Gc)==[1]:continue
 print('ZERO DIMENSIONAL',Gc.is_zero_dimensional,flush=True)
 if Gc.is_zero_dimensional and not modulus:
  L=Gc.fglm('lex');print('LEX',L,flush=True)
  print('SOLUTIONS',S.solve_poly_system(list(L),A,B,K),flush=True)
