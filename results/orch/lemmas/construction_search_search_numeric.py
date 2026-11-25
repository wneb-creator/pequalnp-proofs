import numpy as np
from scipy.optimize import least_squares
from itertools import permutations,combinations
import time,json
from pathlib import Path
coords=[(i,j) for i in range(4) for j in range(i,4)]
lookup={ij:k for k,ij in enumerate(coords)}
ix=[[lookup[tuple(sorted((i,j)))] for j in range(4)] for i in range(4)]
terms=[{} for k in range(5)]
for p in permutations(range(4)):
 for k in range(2,5):
  for I in combinations(range(4),k):
   m=tuple(sorted(ix[i][p[i]] for i in I))
   terms[k][m]=terms[k].get(m,0)+1
packs=[]
for k in range(2,5):
 idx=np.array(list(terms[k])); coeff=np.array(list(terms[k].values()))
 pts=np.array([[a,b,k-a-b] for a in range(k+1) for b in range(k+1-a)],float)/k
 packs.append((idx,coeff,pts))
weights=np.array([1 if i==j else 2 for i,j in coords[:9]])
rng=np.random.default_rng(12337)
best=100; start=time.time()
for trial in range(1000):
 pivots=sorted(rng.choice(9,3,replace=False))
 free=[(i,j) for i in range(3) for j in range(9) if j not in pivots]
 def decode(x):
  A=np.zeros((3,10),complex)
  A[:,pivots]=np.eye(3)
  for n,(i,j) in enumerate(free):A[i,j]=x[n]+1j*x[n+18]
  A[:,9]=-A[:,:9]@weights
  return A
 def funjac(x,jac=False):
  A=decode(x); vals=[];jacs=[]
  for idx,coeff,pts in packs:
   V=pts@A; selected=V[:,idx]; prods=np.prod(selected,axis=2)
   vals.append(prods@coeff)
   if jac:
    grad=np.zeros((len(pts),10),complex)
    for p in range(idx.shape[1]):
     pr=np.prod(np.delete(selected,p,axis=2),axis=2)*coeff
     for j in range(10):grad[:,j]+=np.sum(pr[:,idx[:,p]==j],axis=1)
    jacs.append(np.stack([pts[:,i]*(grad[:,j]-weights[j]*grad[:,9]) for i,j in free],axis=1))
  if jac:
   J=np.concatenate(jacs);return np.block([[J.real,-J.imag],[J.imag,J.real]])
  v=np.concatenate(vals);return np.concatenate([v.real,v.imag])
 x=rng.normal(size=36)*0.5
 res=least_squares(funjac,x,jac=lambda x:funjac(x,True),method='lm',max_nfev=1000,ftol=1e-11,xtol=1e-11,gtol=1e-11)
 norm=np.linalg.norm(res.fun)
 if norm<best:
  best=norm
  print('BEST',trial,'norm',norm,'pivots',pivots,'normA',np.linalg.norm(decode(res.x)),'time',time.time()-start,flush=True)
  A=decode(res.x)
  Path('/tmp/oec/pequalnp-pilot-79/numeric_best.json').write_text(json.dumps({'trial':trial,'norm':norm,'pivots':[int(x) for x in pivots],'A':[[[float(x.real),float(x.imag)] for x in row] for row in A]},indent=2))
 if norm<1e-9:
  print('FOUND',repr(decode(res.x)),flush=True);break
 if trial%10==0:print('PROGRESS',trial,'time',time.time()-start,flush=True)
