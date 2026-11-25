from pathlib import Path
import json,resource,time,itertools
import numpy as np
import sympy as S
from scipy.optimize import least_squares
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,125))
OUT=Path('/tmp/oec/pequalnp-pilot-78/construct_search');data=json.loads((OUT/'tracezero-hadamard.json').read_text());variables=S.symbols(' '.join(data['variables']));indices=[];coeff=[];generators=[]
for g,text in enumerate(data['equations']):
 terms=S.Poly(S.sympify(text.replace('^','**')),*variables).terms();scale=np.sqrt(sum(float(c)**2 for m,c in terms))
 for exp,c in terms:
  m=[i for i,n in enumerate(exp) for _ in range(n)];indices.append(m+[12]*(4-len(m)));coeff.append(float(c)/scale);generators.append(g)
indices=np.array(indices,dtype=np.int64);coeff=np.array(coeff);generators=np.array(generators);active=[indices[:,k]!=12 for k in range(4)]
def evaluate(z,want_jac=False):
 values=np.append(z,1)[indices];result=np.zeros(12,dtype=complex);np.add.at(result,generators,coeff*np.prod(values,axis=1))
 if not want_jac:return result
 jac=np.zeros((12,12),dtype=complex)
 for k in range(4):
  mask=active[k];derivative=np.prod(values[:,[j for j in range(4) if j!=k]],axis=1)*coeff;np.add.at(jac,(generators[mask],indices[mask,k]),derivative[mask])
 return result,jac
def fun(t):
 value=evaluate(t[:12]+1j*t[12:]);return np.r_[value.real,value.imag]
def jac(t):
 _,J=evaluate(t[:12]+1j*t[12:],True);return np.block([[J.real,-J.imag],[J.imag,J.real]])
Q=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2;ij=[(i,j) for i in range(4) for j in range(i,4)];perms=list(itertools.permutations(range(4)))
def matrices(z):
 result=[]
 for n in range(2):
  D=np.array([1-n,n,z[10+n]]);P=np.array([z[2*i+n] for i in range(3)]);B=np.array([z[6+n],z[8+n],-z[6+n]-z[8+n]]);X=(P-D)/2;off=(3*D-P)/2;T=np.array([[0,X[0],X[1],X[2]],[X[0],B[0],off[2],off[1]],[X[1],off[2],B[1],off[0]],[X[2],off[1],off[0],B[2]]]);result.append(Q@T@Q.T)
 return result
def classify(z):
 mats=matrices(z);M=np.array([[T[i,j] for T in mats] for i,j in ij]);orth=np.linalg.qr(M)[0];projector=orth@orth.conj().T;stabilizer=[]
 for p in perms:
  transformed=np.array([[T[p[i],p[j]] for T in mats] for i,j in ij]);err=np.linalg.norm(transformed-projector@transformed)/max(1,np.linalg.norm(transformed))
  if err<1e-6:stabilizer.append(list(p))
 singular=np.linalg.svd(np.vstack(mats),compute_uv=False);_,J=evaluate(z,True)
 return {'stabilizer':stabilizer,'common_kernel_singular_values':singular.tolist(),'jacobian_singular_values':np.linalg.svd(J,compute_uv=False).tolist()},projector
rng=np.random.default_rng(2317812);point=(rng.normal(size=12)+1j*rng.normal(size=12))*.3;_,J=evaluate(point,True);error=0.
for k in range(12):
 step=np.zeros(12);step[k]=1e-6;error=max(error,float(np.max(np.abs((evaluate(point+step)-evaluate(point-step))/(2e-6)-J[:,k]))))
assert error<1e-7,error
print(json.dumps({'phase':'jacobian_check','max_error':error}),flush=True);start=time.process_time();best=float('inf');runs=[];candidates=[];projectors=[]
for run in range(300):
 if time.process_time()-start>107:break
 scale=[.1,.3,.7,1.5,3.,8.][run%6];z=(rng.normal(size=12)+1j*rng.normal(size=12))*scale
 if run%5==0:z=np.asarray(z.real,dtype=complex)
 if run%3!=2:z[:6]+=np.array([1,0,0,1,0,0])*np.sqrt(3)
 result=least_squares(fun,np.r_[z.real,z.imag],jac=jac,method='lm',max_nfev=300,ftol=1e-12,xtol=1e-12,gtol=1e-12);z=result.x[:12]+1j*result.x[12:];residual=float(np.max(np.abs(evaluate(z))));record={'run':run,'scale':scale,'residual_max':residual,'norm':float(np.linalg.norm(z)),'nfev':int(result.nfev),'cpu_seconds':time.process_time()-start};runs.append(record)
 if residual<best:
  best=residual;(OUT/'tracezero-numeric-best.json').write_text(json.dumps({'record':record,'real':z.real.tolist(),'imag':z.imag.tolist()},indent=2))
 if residual<1e-9 and np.linalg.norm(z)<1e5:
  classification,proj=classify(z);duplicate=next((i for i,p in enumerate(projectors) if np.linalg.norm(proj-p)<1e-5),None)
  if duplicate is None:
   candidates.append({'record':record,'real':z.real.tolist(),'imag':z.imag.tolist(),**classification});projectors.append(proj);record['new_candidate']=len(candidates)-1;record['stabilizer_size']=len(classification['stabilizer']);(OUT/'tracezero-numeric-candidates.json').write_text(json.dumps(candidates,indent=2))
  else:record['candidate']=duplicate
 print(json.dumps(record),flush=True)
report={'runs':len(runs),'best_residual':best,'distinct_candidates':len(candidates),'cpu_seconds':time.process_time()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'jacobian_error':error,'scope':'Numerical candidate census only; convergence does not prove exact solutions or complete classification'};(OUT/'tracezero-numeric-summary.json').write_text(json.dumps(report,indent=2));print(json.dumps({'phase':'complete',**report}),flush=True)
