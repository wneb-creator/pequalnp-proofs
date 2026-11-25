import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,sympy as s,itertools as it,math,time,json,resource,signal
from pathlib import Path
from scipy.optimize import least_squares
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));signal.signal(signal.SIGALRM,lambda a,b: (_ for _ in ()).throw(TimeoutError('120-second budget')));signal.alarm(120)
job=Path('/tmp/oec/pequalnp-pilot-79');start=time.monotonic();rng=np.random.default_rng(20261126);pars=s.symbols('l0 m0 l1 m1 l2 m2');C=s.MutableDenseNDimArray.zeros(3,3,3);O={};A={};Q={}
sign={(0,1):1,(1,0):1,(1,2):1,(2,1):1,(0,2):-1,(2,0):-1}
for i in range(3):
 j=(i+1)%3;k=(i+2)%3;l,second=pars[2*i:2*i+2];epsilon,eta=sign[i,j],sign[i,k]
 if epsilon==eta:
  m=second;den=1+l*m;pp=-2*epsilon*l/den;qq=-2*epsilon*m/den;rr=epsilon*(1-l*m)/den
 else:
  m=-1/l;qq=second;rr=epsilon+qq*l;pp=-2*epsilon*l-qq*l*l
 C[j,j,i]=pp;C[k,k,i]=qq;C[j,k,i]=C[k,j,i]=rr;O[i,j]=l;O[i,k]=m
for i,j in it.permutations(range(3),2):
 k=3-i-j;u,v=O[i,j],O[j,i];di,dj=C[k,k,i],C[k,k,j];epsilon=sign[i,j];Q[i,j]=2*epsilon+di*v+dj*u;A[i,j]=-2*epsilon*(v+2*u)-2*di*u*v-dj*u*u
for k in range(3):
 i=(k+1)%3;j=(k+2)%3;C[k,k,k]=(A[i,k]+A[j,k])/2-Q[i,j]
for i,j in it.permutations(range(3),2):C[i,j,i]=C[j,i,i]=(A[i,j]-C[j,j,j])/2
entries=[C[i,j,k] for i in range(3) for j in range(3) for k in range(3)];matrix=s.Matrix(entries);cj=s.lambdify(pars,(matrix,matrix.jacobian(pars)),'numpy',cse=True)
mons=[e for e in it.product(range(5),repeat=4) if sum(e)==4];points=np.array(mons,dtype=float);V=np.array([[np.prod(p**np.array(e)) for e in mons] for p in points]);indices=[i for i,e in enumerate(mons) if e[0]>0 or min(e[1:])>=1];assert len(indices)==23;W=np.linalg.inv(V)[indices];chosen=[mons[i] for i in indices];powers=np.array([e[0] for e in chosen]);multipliers=np.array([24/math.prod(math.factorial(k) for k in e) for e in chosen]);perms=np.array(list(it.permutations(range(4))));rows=np.arange(4);y=points[:,0];t=points[:,1:]
best=1e100;bestdata=None;attempts=0;valid_solutions=0;degenerate_solutions=0

def evaluate(z,want_jac=True):
 c,dc=cj(*z[:6]);c=np.asarray(c,dtype=complex).reshape(3,3,3);dc=np.asarray(dc,dtype=complex).reshape(3,3,3,6);u=np.r_[1,z[6:9]];R=np.outer(u,u);N=np.zeros((35,4,4),dtype=complex);N[:,0,1:]=N[:,1:,0]=t;N[:,1:,1:]=np.einsum('ijk,nk->nij',c,t);M=y[:,None,None]*R+N;vals=M[:,rows,perms];product=np.prod(vals,axis=2);per=product.sum(axis=1);res=W@per-multipliers*z[9]**powers
 if not want_jac:return res
 dM=np.zeros((35,4,4,10),dtype=complex);dM[:,1:,1:,:6]=np.einsum('ijkv,nk->nijv',dc,t)
 for k in range(3):
  du=np.zeros(4);du[k+1]=1;dM[:,:,:,k+6]=y[:,None,None]*(np.outer(du,u)+np.outer(u,du))
 dvals=dM[:,rows,perms,:];other=np.stack([np.prod(vals[:,:,np.arange(4)!=r],axis=2) for r in range(4)],axis=2);jac=W@np.einsum('nprv,npr->nv',dvals,other);jac[:,9]-=multipliers*powers*z[9]**np.maximum(powers-1,0)
 return res,jac
cache_x=None;cache_f=None;cache_j=None

def calc(x):
 global cache_x,cache_f,cache_j
 if cache_x is None or not np.array_equal(x,cache_x):
  z=x[:10]+1j*x[10:];f,j=evaluate(z);cache_x=x.copy();cache_f=np.r_[f.real,f.imag];cache_j=np.block([[j.real,-j.imag],[j.imag,j.real]])
 return cache_f,cache_j
# Verify the analytic Jacobian on a fixed random test point.
z=(rng.normal(size=10)+1j*rng.normal(size=10))*.3;f,j=evaluate(z);step=1e-6;fd=np.stack([(evaluate(z+np.eye(10)[k]*step,False)-evaluate(z-np.eye(10)[k]*step,False))/(2*step) for k in range(10)],axis=1);jac_error=float(np.linalg.norm(j-fd)/max(1,np.linalg.norm(j)));assert jac_error<1e-6
c0=np.asarray(cj(*z[:6])[0],dtype=complex).reshape(3,3,3);u0=np.r_[1,z[6:9]];mesh=np.zeros((35,4,4),dtype=complex);mesh[:,0,1:]=mesh[:,1:,0]=t;mesh[:,1:,1:]=np.einsum('ijk,nk->nij',c0,t);mesh+=y[:,None,None]*np.outer(u0,u0);full=np.linalg.solve(V,np.prod(mesh[:,rows,perms],axis=2).sum(axis=1));omitted=[i for i in range(35) if i not in indices];omitted_error=max(abs(full[i]-24/math.prod(math.factorial(k) for k in mons[i])) for i in omitted);assert omitted_error<1e-7
print(json.dumps({'stage':'ready','seconds':time.monotonic()-start,'jacobian_relative_error':jac_error,'omitted_coefficient_error':float(omitted_error),'classification':'Heuristic complex numerical search; not a proof'}),flush=True)
try:
 for attempt in range(1000):
  attempts=attempt+1;scale=[.3,.8,1.5,3.][attempt%4];z=(rng.normal(size=10)+1j*rng.normal(size=10))*scale;z[6:9]=(rng.normal(size=3)+1j*rng.normal(size=3))*.5+1;z[9]=24**.25*np.sqrt(np.prod(z[6:9]));x=np.r_[z.real,z.imag];x=np.clip(x,-4.9,4.9)
  result=least_squares(lambda x:calc(x)[0],x,jac=lambda x:calc(x)[1],bounds=(-5,5),max_nfev=200,ftol=1e-11,xtol=1e-11,gtol=1e-11)
  score=float(np.linalg.norm(result.fun));zz=result.x[:10]+1j*result.x[10:];den=np.array([1+zz[2]*zz[3],zz[0],zz[4]]);full=float(min(np.abs(zz[6:10])));dmin=float(min(abs(den)))
  if score<best:
   best=score;bestdata={'attempt':attempt,'residual':score,'params':[[float(v.real),float(v.imag)] for v in zz],'min_rankone_scalar_abs':full,'min_denominator_abs':dmin,'evaluations':int(result.nfev)};(job/'construction-toprow-mixed-numeric-best.json').write_text(json.dumps(bestdata,indent=2)+'\n');print(json.dumps({'stage':'best',**bestdata}),flush=True)
  if score<1e-7:
   if full>1e-3 and dmin>1e-3:valid_solutions+=1;break
   degenerate_solutions+=1
except TimeoutError:print('120-second search budget reached',flush=True)
finally:
 summary={'classification':'Heuristic complex numerical search only, not proof','attempts':attempts,'best_residual':best,'valid_numerical_candidates':valid_solutions,'degenerate_numerical_candidates':degenerate_solutions,'seconds':time.monotonic()-start,'jacobian_relative_error':jac_error};(job/'construction-toprow-mixed-numeric-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
