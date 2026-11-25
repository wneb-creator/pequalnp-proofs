from pathlib import Path
import json,resource,time
import numpy as np
from scipy.optimize import least_squares
resource.setrlimit(resource.RLIMIT_AS,(768*2**20,768*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(120,125))
OUT=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard')
data=json.loads((OUT/'chart.json').read_text())
indices=[];coeff=[];generators=[]
for g,f in enumerate(data['polynomials']):
    scale=np.sqrt(sum(c*c for m,c in f))
    for m,c in f:
        indices.append(m+[18]*(4-len(m)));coeff.append(c/scale);generators.append(g)
indices=np.array(indices,dtype=np.int64);coeff=np.array(coeff);generators=np.array(generators)
active=[indices[:,k]!=18 for k in range(4)]
def evaluate(z,want_jac=False):
    extended=np.append(z,1);values=extended[indices]
    products=np.prod(values,axis=1);result=np.zeros(31,dtype=complex)
    np.add.at(result,generators,coeff*products)
    if not want_jac:return result
    jac=np.zeros((31,18),dtype=complex)
    for k in range(4):
        mask=active[k];other=[j for j in range(4) if j!=k]
        derivative=np.prod(values[:,other],axis=1)*coeff
        np.add.at(jac,(generators[mask],indices[mask,k]),derivative[mask])
    return result,jac
def fun(t):
    value=evaluate(t[:18]+1j*t[18:]);return np.r_[value.real,value.imag]
def jac(t):
    value,J=evaluate(t[:18]+1j*t[18:],True)
    return np.block([[J.real,-J.imag],[J.imag,J.real]])
rng=np.random.default_rng(23178);point=(rng.normal(size=18)+1j*rng.normal(size=18))*.3
_,J=evaluate(point,True);error=0.
for k in range(18):
    step=np.zeros(18);step[k]=1e-6
    finite=(evaluate(point+step)-evaluate(point-step))/(2e-6)
    error=max(error,float(np.max(np.abs(finite-J[:,k]))))
assert error<1e-7,error
print(json.dumps({'phase':'jacobian_check','max_error':error}),flush=True)
start=time.process_time();best=float('inf');runs=[]
for run in range(320):
    if time.process_time()-start>110:break
    scale=[.1,.3,.7,1.5,3.,8.][run%6]
    z=(rng.normal(size=18)+1j*rng.normal(size=18))*scale
    if run%4==0:z=np.asarray(z.real,dtype=complex)
    if run%3!=2:
        z[:9]+=np.eye(3).reshape(-1)*np.sqrt(3)*(-1 if run%2 else 1)
    x=np.r_[z.real,z.imag]
    result=least_squares(fun,x,jac=jac,method='lm',max_nfev=220,ftol=1e-10,xtol=1e-10,gtol=1e-10)
    z=result.x[:18]+1j*result.x[18:];residual=float(np.max(np.abs(evaluate(z))))
    record={'run':run,'scale':scale,'residual_max':residual,'norm':float(np.linalg.norm(z)),'nfev':int(result.nfev),'cpu_seconds':time.process_time()-start}
    runs.append(record);print(json.dumps(record),flush=True)
    if residual<best:
        best=residual
        (OUT/'numeric-best.json').write_text(json.dumps({'record':record,'real':z.real.tolist(),'imag':z.imag.tolist(),'residual_real':evaluate(z).real.tolist(),'residual_imag':evaluate(z).imag.tolist()},indent=2))
    if residual<1e-10:break
report={'runs':len(runs),'best_residual':best,'cpu_seconds':time.process_time()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'jacobian_error':error,'scope':'Numerical candidate search only; nonzero residual does not imply nonexistence'}
(OUT/'numeric-summary.json').write_text(json.dumps(report,indent=2));print(json.dumps({'phase':'complete',**report}),flush=True)
