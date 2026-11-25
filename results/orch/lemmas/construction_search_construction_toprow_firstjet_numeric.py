import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,sympy as s,itertools as it,math,time,json,resource,signal
from pathlib import Path
from scipy.optimize import least_squares
from scipy.linalg import qr
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));signal.signal(signal.SIGALRM,lambda a,b: (_ for _ in ()).throw(TimeoutError('120-second budget')));signal.alarm(120)
job=Path('/tmp/oec/pequalnp-pilot-79');start=time.monotonic();rng=np.random.default_rng(20261125);pars=s.symbols('l0 m0 l1 m1 l2 m2');C=s.MutableDenseNDimArray.zeros(3,3,3);O={};A={};Q={}
for i in range(3):
 j=(i+1)%3;k=(i+2)%3;l,m=pars[2*i:2*i+2];den=1+l*m;C[j,j,i]=-2*l/den;C[k,k,i]=-2*m/den;C[j,k,i]=C[k,j,i]=(1-l*m)/den;O[i,j]=l;O[i,k]=m
for i,j in it.permutations(range(3),2):
 k=3-i-j;u,v=O[i,j],O[j,i];di,dj=C[k,k,i],C[k,k,j];Q[i,j]=2+di*v+dj*u;A[i,j]=-2*(v+2*u)-2*di*u*v-dj*u*u
for k in range(3):
 i=(k+1)%3;j=(k+2)%3;C[k,k,k]=(A[i,k]+A[j,k])/2-Q[i,j]
for i,j in it.permutations(range(3),2):C[i,j,i]=C[j,i,i]=(A[i,j]-C[j,j,j])/2
entries=[C[i,j,k] for i in range(3) for j in range(3) for k in range(3)];matrix=s.Matrix(entries);cj=s.lambdify(pars,(matrix,matrix.jacobian(pars)),'numpy',cse=True)
mons3=[e for e in it.product(range(4),repeat=3) if sum(e)==3];t3=np.array(mons3,float);V3=np.array([[np.prod(t**np.array(e)) for e in mons3] for t in t3]);W3=np.linalg.inv(V3)
mons4=[e for e in it.product(range(5),repeat=3) if sum(e)==4];t4=np.array(mons4,float);V4=np.array([[np.prod(t**np.array(e)) for e in mons4] for t in t4]);W4=np.linalg.inv(V4)[[i for i,e in enumerate(mons4) if min(e)>=1]]
edges=list(it.combinations_with_replacement(range(3),2));basis=np.zeros((3,3,6),complex)
for h,(i,j) in enumerate(edges):basis[i,j,h]=basis[j,i,h]=1
perms3=list(it.permutations(range(3)));perms4=np.array(list(it.permutations(range(4))));rows4=np.arange(4)
monsfull=[e for e in it.product(range(5),repeat=4) if sum(e)==4];meshfull=np.array(monsfull,float);Vfull=np.array([[np.prod(t**np.array(e)) for e in monsfull] for t in meshfull]);Wfull=np.linalg.inv(Vfull);higher=[i for i,e in enumerate(monsfull) if e[0]>=2];fullweights=np.array([24/math.prod(math.factorial(k) for k in e) for e in monsfull]);fullpowers=np.array([e[0] for e in monsfull])

def kmat(S):
 out=np.zeros_like(S)
 for i in range(3):
  a,b=[k for k in range(3) if k!=i]
  for j in range(3):
   c,d=[k for k in range(3) if k!=j];out[:,i,j]=S[:,a,c]*S[:,b,d]+S[:,a,d]*S[:,b,c]
 return out

def dk(S,dS):
 out=np.empty_like(dS)
 for i in range(3):
  a,b=[k for k in range(3) if k!=i]
  for j in range(3):
   c,d=[k for k in range(3) if k!=j];out[:,i,j,:]=dS[:,a,c,:]*S[:,b,d,None]+S[:,a,c,None]*dS[:,b,d,:]+dS[:,a,d,:]*S[:,b,c,None]+S[:,a,d,None]*dS[:,b,c,:]
 return out

def a_six(S):return W3@np.einsum('ni,nijh,nj->nh',t3,dk(S,np.broadcast_to(basis,(10,3,3,6))),t3)

def all_data(z):
 c,dc=cj(*z);c=np.asarray(c,complex).reshape(3,3,3);dc=np.asarray(dc,complex).reshape(3,3,3,6);S3=np.einsum('ijk,nk->nij',c,t3);dS3=np.einsum('ijkv,nk->nijv',dc,t3);S4=np.einsum('ijk,nk->nij',c,t4);dS4=np.einsum('ijkv,nk->nijv',dc,t4)
 A=np.c_[a_six(S3),-4*(W3@(t3.sum(axis=1)**3))];g=W3@sum(S3[:,0,u]*S3[:,1,v]*S3[:,2,w] for u,v,w in perms3)
 dA=np.zeros((10,7,6),complex)
 for j in range(6):dA[:,:6,j]=a_six(dS3[:,:,:,j])
 dg=W3@np.einsum('nij,nijv->nv',kmat(S3),dS3);q=W4@np.einsum('ni,nij,nj->n',t4,kmat(S4),t4)-12;dq=W4@np.einsum('ni,nijv,nj->nv',t4,dk(S4,dS4),t4)
 return c,A,g,dA,dg,q,dq

def solve_data(z,pivots):
 c,A,g,dA,dg,q,dq=all_data(z);rest=[j for j in range(10) if j not in pivots];M=A[pivots];unknown=np.linalg.solve(M,-g[pivots]);du=np.linalg.solve(M,-dg[pivots]-np.einsum('nkv,k->nv',dA[pivots],unknown));jet=A[rest]@unknown+g[rest];dj=np.einsum('nkv,k->nv',dA[rest],unknown)+A[rest]@du+dg[rest]
 return np.r_[q,jet],np.vstack([dq,dj]),(c,A,g,unknown)

def higher_residual(c,unknown):
 H=np.zeros((4,4),complex);H[0,0]=1
 for (i,j),value in zip(edges,unknown[:6]):H[i+1,j+1]=H[j+1,i+1]=value
 t=meshfull[:,1:];M=meshfull[:,0,None,None]*H;M[:,0,1:]+=t;M[:,1:,0]+=t;M[:,1:,1:]+=np.einsum('ijk,nk->nij',c,t);per=np.prod(M[:,rows4,perms4],axis=2).sum(axis=1);res=Wfull@per-fullweights*unknown[6]**fullpowers
 return float(np.linalg.norm(res[higher]))

solutions=[];attempts=0;best=1e100;full_candidates=0;cache_x=None;cache_f=None;cache_j=None;current_pivots=None

def calc(x):
 global cache_x,cache_f,cache_j
 if cache_x is None or not np.array_equal(x,cache_x):
  f,j,_=solve_data(x[:6]+1j*x[6:],current_pivots);cache_x=x.copy();cache_f=np.r_[f.real,f.imag];cache_j=np.block([[j.real,-j.imag],[j.imag,j.real]])
 return cache_f,cache_j
z=(rng.normal(size=6)+1j*rng.normal(size=6))*.3;_,A,*_=all_data(z);testp=list(qr(A.T,pivoting=True)[2][:7]);f,j,_=solve_data(z,testp);step=1e-6;fd=np.stack([(solve_data(z+np.eye(6)[k]*step,testp)[0]-solve_data(z-np.eye(6)[k]*step,testp)[0])/(2*step) for k in range(6)],axis=1);error=float(np.linalg.norm(fd-j)/max(1,np.linalg.norm(j)));assert error<1e-5
print(json.dumps({'stage':'ready','analytic_jacobian_relative_error':error,'seconds':time.monotonic()-start,'classification':'Heuristic first-jet root search, not a proof'}),flush=True)
try:
 for attempt in range(1000):
  attempts=attempt+1;scale=[.3,.8,1.5,3.][attempt%4];z=(rng.normal(size=6)+1j*rng.normal(size=6))*scale;x=np.clip(np.r_[z.real,z.imag],-9.9,9.9);z=x[:6]+1j*x[6:];_,A,*_=all_data(z);current_pivots=list(qr(A.T,pivoting=True)[2][:7]);cache_x=None
  try:result=least_squares(lambda x:calc(x)[0],x,jac=lambda x:calc(x)[1],bounds=(-10,10),max_nfev=150,ftol=1e-11,xtol=1e-11,gtol=1e-11)
  except (np.linalg.LinAlgError,FloatingPointError,ValueError):continue
  score=float(np.linalg.norm(result.fun));best=min(best,score)
  if score>1e-7:continue
  zz=result.x[:6]+1j*result.x[6:];res,jac,(c,A,g,unknown)=solve_data(zz,current_pivots);condition=float(np.linalg.cond(A[current_pivots]));den=min(abs(1+zz[2*i]*zz[2*i+1]) for i in range(3))
  if condition>1e9 or den<1e-4:continue
  if any(np.linalg.norm(zz-np.array([complex(*a) for a in entry['params']]))<1e-4*(1+np.linalg.norm(zz)) for entry in solutions):continue
  high=higher_residual(c,unknown);full_candidates+=high<1e-7
  entry={'attempt':attempt,'residual':score,'higher_jet_residual':high,'condition':condition,'jacobian_rank':int(np.linalg.matrix_rank(jac,tol=1e-6)),'params':[[float(a.real),float(a.imag)] for a in zz],'extension':[[float(a.real),float(a.imag)] for a in unknown]};solutions.append(entry);(job/'construction-toprow-firstjet-solutions.json').write_text(json.dumps(solutions,indent=2)+'\n');print(json.dumps({'stage':'new_jet_point','count':len(solutions),**entry}),flush=True)
except TimeoutError:print('120-second search budget reached',flush=True)
finally:
 summary={'classification':'Heuristic complex first-jet search, not proof','attempts':attempts,'distinct_first_jet_points':len(solutions),'full_space_candidates':int(full_candidates),'best_residual':best,'seconds':time.monotonic()-start,'analytic_jacobian_relative_error':error};(job/'construction-toprow-firstjet-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
