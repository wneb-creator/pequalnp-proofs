import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import json,time
from pathlib import Path
import numpy as np
import sympy as s
from scipy.optimize import least_squares
base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
data=json.loads((base/'star-full-generate-equations.json').read_text())
u=s.symbols(' '.join(data['unknowns']))
f=s.Matrix([s.sympify(r['coefficient'],locals=dict(zip(data['unknowns'],u))) for r in data['equations']])
fun=s.lambdify([u],f,'numpy',cse=True);jac=s.lambdify([u],f.jacobian(u),'numpy',cse=True)
def unpack(v):return v[:18]+1j*v[18:]
def F(v):
 r=np.asarray(fun(unpack(v)),complex).ravel()
 return np.r_[r.real,r.imag]
def J(v):
 r=np.asarray(jac(unpack(v)),complex)
 return np.block([[r.real,-r.imag],[r.imag,r.real]])
rng=np.random.default_rng(23175)
best=1e99;start=time.monotonic()
for k in range(1000):
 scale=[.1,.3,1.,3.,10.][k%5]
 v=rng.normal(size=36)*scale
 out=least_squares(F,v,jac=J,max_nfev=1500,ftol=1e-12,xtol=1e-12,gtol=1e-12)
 err=np.linalg.norm(F(out.x),np.inf)
 print(k,'err',err,'norm',np.linalg.norm(out.x),'nfev',out.nfev,'time',time.monotonic()-start,flush=True)
 if err<best:
  best=err
  (base/'numeric-star-best.json').write_text(json.dumps({'seed':k,'error':err,'norm':float(np.linalg.norm(out.x)),'unknowns':data['unknowns'],'values':[[float(v.real),float(v.imag)] for v in unpack(out.x)]},indent=2))
  print('BEST',best,repr(unpack(out.x)),flush=True)
 if err<1e-9:break
 if time.monotonic()-start>300:break
