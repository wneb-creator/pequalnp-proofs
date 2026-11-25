from pathlib import Path
import sympy as s,itertools,json
job=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
Q=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
P=s.Matrix(3,3,s.symbols('p0:9'));B=s.Matrix(3,3,s.symbols('b0:9'));D=s.Matrix(s.symbols('D0:3'))
def chart(P,B,D):
 p=P*D;bb=B*D;v=(p-D)/2;o=(3*D-p)/2
 T=s.Matrix([[0,v[0],v[1],v[2]],[v[0],bb[0],o[2],o[1]],[v[1],o[2],bb[1],o[0]],[v[2],o[1],o[0],bb[2]]])
 return T
T=chart(P,B,D);actions=[];vars=list(P)+list(B)
for perm in itertools.permutations(range(4)):
 S=s.zeros(4)
 for i,j in enumerate(perm):S[i,j]=1
 RR=Q.T*S*Q;R=RR[1:,1:]
 assert RR==s.diag(s.ones(1),R)
 assert all(sum(1 for x in R.row(i) if x)!=0 for i in range(3))
 signs=[next(x for x in R.row(i) if x) for i in range(3)]
 assert s.prod(signs)==1
 U=R.applyfunc(abs)
 Pp=R*P*R.T;Bp=U*B*R.T
 difference=chart(Pp,Bp,R*D)-RR*T*RR.T
 assert all(s.expand(x)==0 for x in difference)
 action=[]
 for v in list(Pp)+list(Bp):
  for k,x in enumerate(vars):
   if v==x:action.append([k,1]);break
   if v==-x:action.append([k,-1]);break
  else:raise ValueError(v)
 actions.append({'permutation':perm,'R':[[int(x) for x in row] for row in R.tolist()],'variables':action})
print('ALL24 MATRIXEQUIVARIANCE PASSED')
print('VARIABLES',vars)
(job/'s4-hadamard-actions.json').write_text(json.dumps(actions,indent=2))
p=P*D;bb=B*D;v=(p-D)/2;o=(3*D-p)/2
q=sum(bb[i]**2+2*o[i]**2-6*v[i]**2 for i in range(3))
assert s.expand(q-sum(bb[i]**2-p[i]**2+3*D[i]**2 for i in range(3)))==0
print('QUADRATIC NORMALFORM PASSED')
