import sympy as s,itertools,json,time,math,random,sys,multiprocessing as mp
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
data=json.loads((base/'c4-support-homogeneous.json').read_text())
vs=list(s.symbols('v:7'));Hs={k:s.sympify(data['homogeneous'][str(k)]) for k in [2,3,4]}
G=s.hessian(Hs[2],vs)/2
def primitive(v):
 dd=s.ilcm(*[x.q for x in v]);vv=dd*v
 return vv/s.igcd(*[int(x) for x in vv])
def ratnull(Q):
 n=Q.rows
 for support_size in [1,2,3]:
  for support in itertools.combinations(range(n),support_size):
   for coeff in itertools.product([1,-1,2,-2,3,-3],repeat=support_size-1):
    e=s.zeros(n,1)
    for j,x in zip(support,(1,)+coeff):e[j]=x
    if (e.T*Q*e)[0]==0:return e
 rng=random.Random(231)
 for trial in range(20000):
  j=trial%n
  if Q[j,j]==0:continue
  v=[rng.randint(-8,8) if i!=j else 0 for i in range(n)]
  aa=int(Q[j,j]);bb=2*sum(int(Q[j,i])*v[i] for i in range(n))
  cc=sum(int(Q[i,k])*v[i]*v[k] for i in range(n) for k in range(n))
  dd=bb*bb-4*aa*cc
  if dd<0 or math.isqrt(dd)**2!=dd:continue
  v[j]=s.Rational(-bb+math.isqrt(dd),2*aa)
  if any(v):return primitive(s.Matrix(v))
 raise RuntimeError('rational null search failed')
R=s.eye(7);EE=[];FF=[]
for step in range(2):
 Q=R.T*G*R;e=ratnull(Q)
 j=next(j for j in range(Q.rows) if (e.T*Q)[j])
 f=s.eye(Q.rows)[:,j];b=(e.T*Q*f)[0]
 f=f/b-(f.T*Q*f)[0]/(2*b*b)*e
 EE.append(R*e);FF.append(R*f)
 R=R*s.Matrix.hstack(*[primitive(z) for z in s.Matrix.vstack(e.T*Q,f.T*Q).nullspace()])
Q=R.T*G*R
choices=[]
for i,j in itertools.combinations(range(3),2):
 aa,bb,cc=Q[i,i],Q[i,j],Q[j,j];disc=bb*bb-aa*cc
 if cc and disc:choices.append((s.count_ops(s.sqrt(disc)),i,j,aa,bb,cc,disc))
_,i,j,aa,bb,cc,disc=min(choices,key=lambda z:z[:3]);root=s.sqrt(disc)
e=s.zeros(3,1);f=s.zeros(3,1);e[i]=f[i]=1;e[j]=(-bb+root)/cc;f[j]=(-bb-root)/cc
f=(f/(e.T*Q*f)[0]).applyfunc(s.simplify)
EE.append((R*e).applyfunc(s.simplify));FF.append((R*f).applyfunc(s.simplify))
last=s.Matrix.hstack(*s.Matrix.vstack(e.T*Q,f.T*Q).nullspace())
Z=(R*last).applyfunc(s.simplify);dd=s.simplify((Z.T*G*Z)[0])
E=s.Matrix.hstack(*EE);F=s.Matrix.hstack(*FF)
assert s.simplify(E.T*G*E)==s.zeros(3) and s.simplify(F.T*G*F)==s.zeros(3)
assert s.simplify(E.T*G*F)==s.eye(3) and s.simplify(Z.T*G*E)==s.zeros(1,3) and s.simplify(Z.T*G*F)==s.zeros(1,3)
assert s.simplify(s.Matrix.hstack(E,F,Z).det())!=0
print('FRAME root',root,'residual norm',dd,'E',E,'F',F,'Z',Z,flush=True)
def worker(chart,queue):
 params=s.symbols('a:6');X=s.Matrix(s.symbols('x y z'))
 K=s.Matrix([[0,params[0],params[1]],[-params[0],0,params[2]],[-params[1],-params[2],0]])
 rr=s.Matrix(1,3,params[3:]);Y=(K-dd*rr.T*rr/2)*X
 left=s.Matrix([Y[i] if chart>>i&1 else X[i] for i in range(3)])
 right=s.Matrix([X[i] if chart>>i&1 else Y[i] for i in range(3)])
 vec=E*left+F*right+Z*(rr*X)[0]
 assert s.simplify((vec.T*G*vec)[0])==0
 eq=[]
 sub=dict(zip(vs,vec))
 for degree in [3,4]:
  pp=s.Poly(s.expand(Hs[degree].subs(sub,simultaneous=True)),*X)
  for mon,c in pp.terms():
   cc=s.Poly(c,*params,extension=True).clear_denoms()[1].as_expr()
   if cc!=0:eq.append(cc)
 (base/('c4-support-chart-'+str(chart)+'.json')).write_text(json.dumps({'parameters':list(map(str,params)),'equations':list(map(str,eq))},indent=2))
 print('CHART',chart,'equations exported',len(eq),flush=True)
 start=time.monotonic();basis=s.groebner(eq,*params,extension=True,order='grevlex')
 queue.put({'chart':chart,'basis':list(map(str,basis)),'unit_ideal':list(basis)==[1],'seconds':time.monotonic()-start})
if __name__=='__main__':
 charts=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else list(range(8))
 for chart in charts:
  queue=mp.Queue();p=mp.Process(target=worker,args=(chart,queue));p.start();p.join(120)
  if p.is_alive():p.terminate();p.join();print({'chart':chart,'status':'UNKNOWN_TIME_LIMIT'},flush=True)
  elif p.exitcode:print({'chart':chart,'status':'ERROR','exit':p.exitcode},flush=True)
  else:print(queue.get(),flush=True)
