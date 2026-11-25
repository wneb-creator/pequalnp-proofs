import sympy as s,itertools
xs=s.symbols('x:9');h=s.symbols('h');coords=[(i,j) for i in range(4) for j in range(i,4)];T=s.zeros(4)
for a,(i,j) in zip(xs,coords[:-1]):T[i,j]=T[j,i]=a
T[3,3]=-sum(T[i,j] for i in range(4) for j in range(4))
P=s.Poly(s.expand(sum(s.prod(1+h*T[i,pi[i]] for i in range(4)) for pi in itertools.permutations(range(4)))),h)
gs=[[s.diff(P.coeff_monomial(h**d),x) for x in xs] for d in [2,3,4]]
for name,A,B in [
 ('star',[0,1,0,-1,0,0,0,0,0],[0,0,1,-1,0,0,0,0,0]),
 ('crossed_star',[0,1,0,0,0,-s.Rational(1,2),-s.Rational(1,2),0,0],[0,0,1,-1,0,0,0,0,0])]:
 A=s.Matrix(A);B=s.Matrix(B);rows=[];krows=[]
 for d,g in zip([2,3,4],gs):
  for t in range(d+1):
   sub=dict(zip(xs,A+t*B));v=[s.expand(e.subs(sub)) for e in g];rows.append(v+[t*e for e in v])
   if t<d:krows.append(v)
 J=s.Matrix(rows);K=s.Matrix(krows)
 print(name,'Jacobian rank',J.rank(),'Kdim',9-K.rank(),'Jacobian',J,'K',K,flush=True)
