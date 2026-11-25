import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import json,time,numpy as np,sympy as s
from scipy.optimize import least_squares
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
d=json.loads((base/'zero-edge-pencil.json').read_text())
v=s.symbols(' '.join(d['variables'])); eq=s.Matrix([s.sympify(e) for e in d['equations']])
fn=s.lambdify([v],eq,'numpy',cse=True); jn=s.lambdify([v],eq.jacobian(v),'numpy',cse=True)
def fun(u):
 z=u[:12]+1j*u[12:];r=np.asarray(fn(z),complex).reshape(-1);return np.r_[r.real,r.imag]
def jac(u):
 z=u[:12]+1j*u[12:];j=np.asarray(jn(z),complex);return np.block([[j.real,-j.imag],[j.imag,j.real]])
rng=np.random.default_rng(148923);start=time.monotonic();best=1e100;roots=[]
for run in range(80):
 if time.monotonic()-start>75:break
 scale=[0.1,0.3,1,3][run%4]
 u=rng.normal(size=24)*scale
 fit=least_squares(fun,u,jac=jac,max_nfev=700,ftol=1e-12,xtol=1e-12,gtol=1e-12)
 z=fit.x[:12]+1j*fit.x[12:];err=np.max(abs(fun(fit.x)));best=min(best,err)
 if err<1e-8:
  D=np.array([[z[0],z[1]],[z[2],z[3]],[z[4],z[5]],[-z[0]-z[2]-z[4]-2*(1+z[6]+z[8]+z[10]),-z[1]-z[3]-z[5]-2*(1+z[7]+z[9]+z[11])]])
  sv=np.linalg.svd(D,compute_uv=False)
  print('ROOT',run,'ERROR',err,'DIAG_SINGULAR_VALUES',sv.tolist(),'COEFF_NORM',np.linalg.norm(z),flush=True)
  roots.append({'run':run,'error':float(err),'diag_sv':sv.tolist(),'real':z.real.tolist(),'imag':z.imag.tolist()})
  if sv[1]>1e-5:
   print('POSSIBLE_RANK_TWO_COUNTEREXAMPLE',z.tolist(),flush=True)
   break
 else:print('NO_ROOT',run,'ERROR',err,flush=True)
(base/'zero-edge-numeric-roots.json').write_text(json.dumps(roots,indent=2))
print('DONE','BEST',best,'SECONDS',time.monotonic()-start,flush=True)
