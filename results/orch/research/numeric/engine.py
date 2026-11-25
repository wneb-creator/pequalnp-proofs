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

