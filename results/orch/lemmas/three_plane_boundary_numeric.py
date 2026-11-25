from pathlib import Path
from datetime import datetime,timezone
import sympy as s,numpy as np,scipy.optimize as opt,itertools,json,time
job=Path('/tmp/oec/pequalnp-pilot-79');t0=time.time();z=s.symbols('z0:9');positions=[(0,0),(1,1),(2,2),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
M=s.zeros(4)
for a,(i,j) in zip(z,positions):M[i,j]=M[j,i]=a
M[3,3]=-sum(z[:3])-2*sum(z[3:]);funs=[];dfs=[];pts=[]
for k in [2,3,4]:
 f=s.expand(sum(s.prod(M[i,p[i]] for i in inds) for p in itertools.permutations(range(4)) for inds in itertools.combinations(range(4),k)))/s.factorial(4-k)
 funs.append(s.lambdify(z,f,'numpy',cse=True));dfs.append(s.lambdify(z,[s.diff(f,a) for a in z],'numpy',cse=True));pts.append(np.array([(j,k-j) for j in range(k+1)],dtype=float).T/k)
B0=np.array([1,0,0,0,0,-1,0,0,0],dtype=complex);DB=np.zeros((9,12),dtype=complex)
for j,row in enumerate([1,2,3,4,6]):DB[row,j]=1
DB[5,2]=DB[5,3]=-1;DB[7,0]=DB[7,2]=DB[7,4]=-1;DB[8,1]=DB[8,3]=DB[8,4]=-1
A0=np.zeros(9,dtype=complex);A0[3]=1;DA=np.zeros((9,12),dtype=complex)
for j,row in enumerate([1,2,4,5,6,7,8]):DA[row,5+j]=1
rng=np.random.default_rng(2317912);best=1e100

def matrices(v):
 c=v[:12]+1j*v[12:];return B0+DB@c,A0+DA@c

def calc(v,jac=False):
 B,A=matrices(v);vals=[];js=[]
 for fn,df,P in zip(funs,dfs,pts):
  Z=B[:,None]*P[0]+A[:,None]*P[1];values=np.broadcast_to(fn(*Z),(P.shape[1],));vals.append(values)
  if jac:
   G=np.array([np.broadcast_to(w,(P.shape[1],)) for w in df(*Z)])
   J=np.einsum('ij,ik,j->jk',G,DB,P[0])+np.einsum('ij,ik,j->jk',G,DA,P[1]);js.append(J)
 if not jac:
  V=np.concatenate(vals);return np.r_[V.real,V.imag]
 J=np.vstack(js);return np.block([[J.real,-J.imag],[J.imag,J.real]])

for run in range(1000):
 start=rng.normal(size=24)*(.3 if run%3==0 else 1)
 sol=opt.least_squares(calc,start,jac=lambda v:calc(v,True),bounds=(-20,20),max_nfev=1000,ftol=1e-12,gtol=1e-12,xtol=1e-12)
 err=np.linalg.norm(sol.fun);B,A=matrices(sol.x)
 if err<best:
  best=err;result={'run':run,'error':err,'Areal':A.real.tolist(),'Aimag':A.imag.tolist(),'Breal':B.real.tolist(),'Bimag':B.imag.tolist(),'nfev':sol.nfev,'seconds':time.time()-t0};(job/'boundary_numeric_best.json').write_text(json.dumps(result,indent=2));print('BEST',result,flush=True)
 if err<1e-9:
  print('FOUND_BOUNDARY',flush=True);break
 if time.time()-t0>110:print('TIME_LIMIT',flush=True);break
print('DONE',best,time.time()-t0,flush=True)
