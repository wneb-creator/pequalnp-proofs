from pathlib import Path
import numpy as np
from scipy.optimize import least_squares
import itertools,json,time,sys
BASE=Path('/tmp/oec/pequalnp-pilot-78/numeric')
coords=[(i,j) for i in range(4) for j in range(i,4)]
weights=np.array([1 if i==j else 2 for i,j in coords],dtype=float)
lookup={p:k for k,p in enumerate(coords)}
exps=[e for d in range(5) for e in itertools.product(range(d+1),repeat=3) if sum(e)==d]
expindex={e:i for i,e in enumerate(exps)}
idx=[];ci=[]
for perm in itertools.permutations(range(4)):
 cs=[lookup[tuple(sorted((r,perm[r])))] for r in range(4)]
 for choices in itertools.product(range(4),repeat=4):
  idx.append([30 if k==0 else cs[r]*3+k-1 for r,k in enumerate(choices)])
  ci.append(expindex[tuple(choices.count(k) for k in (1,2,3))])
ALLIDX=np.array(idx);ALLCI=np.array(ci)
active=np.array([i for i,e in enumerate(exps) if sum(e)>=2])
scales=np.array([2 if sum(exps[i])==2 else 1 for i in active],dtype=float)

class Chart:
 def __init__(self,pivots):
  self.pivots=tuple(pivots)
  self.dep=next(i for i,(r,c) in enumerate(coords) if r==c and i not in pivots)
  self.free=[i for i in range(10) if i not in pivots and i!=self.dep]
  self.fixed=np.zeros((10,3),complex)
  for k,p in enumerate(pivots):self.fixed[p,k]=1
  zeros={p*3+k for j,p in enumerate(pivots) for k in range(3) if k!=j}
  keep=np.array([not any(k in zeros for k in row) for row in ALLIDX])
  self.idx=ALLIDX[keep];self.ci=ALLCI[keep]
  self.deridx=[self.ci*30+np.minimum(self.idx[:,r],29) for r in range(4)]
  self.dermask=[self.idx[:,r]<30 for r in range(4)]
  self.last=None
 def matrix(self,x):
  U=self.fixed.copy();U[self.free,:]=(x[:18]+1j*x[18:]).reshape(6,3)
  U[self.dep,:]=-np.sum(U*weights[:,None],axis=0)/weights[self.dep]
  return U
 def calculate(self,x):
  if self.last is not None and np.array_equal(x,self.last):return
  U=self.matrix(x);signals=np.r_[U.reshape(-1),1]
  F=signals[self.idx];prod=np.prod(F,axis=1)
  vals=np.bincount(self.ci,weights=prod.real,minlength=35)+1j*np.bincount(self.ci,weights=prod.imag,minlength=35)
  deriv=np.zeros(35*30,complex)
  for r in range(4):
   dp=np.prod(F[:,[j for j in range(4) if j!=r]],axis=1)
   mask=self.dermask[r];ids=self.deridx[r][mask];dp=dp[mask]
   deriv+=np.bincount(ids,weights=dp.real,minlength=35*30)+1j*np.bincount(ids,weights=dp.imag,minlength=35*30)
  D=deriv.reshape(35,10,3)[active]
  J=(D[:,self.free,:]-D[:,self.dep:self.dep+1,:]*(weights[self.free]/weights[self.dep])[None,:,None]).reshape(31,18)/scales[:,None]
  v=vals[active]/scales
  self.f=np.r_[v.real,v.imag];self.j=np.block([[J.real,-J.imag],[J.imag,J.real]])
  self.vals=vals;self.last=x.copy()
 def fun(self,x):self.calculate(x);return self.f
 def jac(self,x):self.calculate(x);return self.j

rng=np.random.default_rng(23178)
c=Chart((0,1,2));x=rng.normal(size=36)*0.2
v=rng.normal(size=36);eps=1e-6
err=np.max(np.abs((c.fun(x+eps*v)-c.fun(x-eps*v))/(2*eps)-c.jac(x)@v))
assert err<1e-6,err
print(json.dumps({'jacobian_max_error':float(err),'coordinates':coords}),flush=True)
start=time.monotonic();best=float('inf');allcharts=list(itertools.combinations(range(10),3));rng.shuffle(allcharts)
limit=int(sys.argv[1]) if len(sys.argv)>1 else 240
for attempt in range(limit):
 pivots=allcharts[attempt%len(allcharts)]
 chart=Chart(pivots)
 scale=[0.1,0.3,0.7,1.5][(attempt//len(allcharts))%4]
 x0=rng.normal(size=36)*scale
 result=least_squares(chart.fun,x0,jac=chart.jac,method='lm',max_nfev=500,ftol=1e-12,xtol=1e-12,gtol=1e-12)
 residual=float(np.max(np.abs(chart.fun(result.x))))
 row={'attempt':attempt,'seconds':round(time.monotonic()-start,3),'pivots':pivots,'scale':scale,'max_residual':residual,'cost':float(result.cost),'nfev':result.nfev,'norm':float(np.linalg.norm(result.x)),'optimality':float(result.optimality)}
 if residual<best:
  best=residual
  U=chart.matrix(result.x)
  row['U_real']=U.real.tolist();row['U_imag']=U.imag.tolist()
  (BASE/'best.json').write_text(json.dumps(row,indent=2))
  print(json.dumps({'new_best':row}),flush=True)
 if residual<1e-8:
  (BASE/f'candidate-{attempt}.json').write_text(json.dumps(row,indent=2))
  print(json.dumps({'CANDIDATE':row}),flush=True)
  break
 if attempt%10==0:print(json.dumps({'progress':row,'best':best}),flush=True)
 with (BASE/'runs.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps({'finished':attempt+1,'seconds':time.monotonic()-start,'best':best}),flush=True)
