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
for k in range(3,5):
 idx=np.array(list(terms[k])); coeff=np.array(list(terms[k].values()))
 pts=np.array([[a,b,k-a-b] for a in range(k+1) for b in range(k+1-a)],float)/k
 packs.append((idx,coeff,pts))
H=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],complex)
D=np.diag([1,2,-6])
def convert(p,r,w):
 a=p[0]+r[0];b=1j*(p[0]-r[0]);d=p[1]+r[1]/2;e=1j*(p[1]-r[1]/2);x=p[2]-r[2]/6;y=1j*(p[2]+r[2]/6)
 c,f,z=w
 B=np.array([[0,x,y,z],[x,a,d,e],[y,d,b,f],[z,e,f,c]])
 t=H@B@H/4
 return np.array([t[i,j] for i,j in coords])
Ts=[]
for slot in range(3):
 rows=[]
 for n in range(3):
  args=[np.zeros(3,complex) for _ in range(3)];args[slot][n]=1
  rows.append(convert(*args))
 Ts.append(np.array(rows))
Tp,Tr,Tw=Ts
Toriginal=np.concatenate(Ts,axis=0)
G=np.zeros((9,9),complex);G[:3,3:6]=2*np.eye(3);G[3:6,:3]=2*np.eye(3);G[6:,6:]=D
U=np.zeros((9,9),complex);U[:3,:3]=np.eye(3);U[:3,3:6]=np.eye(3);U[3:6,:3]=1j*np.eye(3);U[3:6,3:6]=-1j*np.eye(3);U[6:,6:]=np.diag([1,np.sqrt(2),1j*np.sqrt(6)]);Ui=np.linalg.inv(U)
S=[]
for a,b in [(0,1),(0,2),(1,2)]:
 s=np.zeros((3,3),complex);s[a,b]=1;s[b,a]=-1;S.append(s)
E=[]
for a in range(3):
 for b in range(3):
  e=np.zeros((3,3),complex);e[a,b]=1;E.append(e)
def decode(v,jac=False):
 M=v[:9].reshape((3,3));skew=sum(v[9+i]*S[i] for i in range(3));K=skew-M.T@D@M/4
 A=Tp+K.T@Tr+M.T@Tw
 if not jac:return A
 ds=[]
 for e in E:
  dk=-(e.T@D@M+M.T@D@e)/4
  ds.append(dk.T@Tr+e.T@Tw)
 ds.extend(s.T@Tr for s in S)
 return A,np.array(ds)
def funjac(x,jac=False):
 v=x[:12]+1j*x[12:]
 if jac:A,ds=decode(v,True)
 else:A=decode(v)
 vals=[];jacs=[]
 for idx,coeff,pts in packs:
  V=pts@A;selected=V[:,idx];vals.append(np.prod(selected,axis=2)@coeff)
  if jac:
   grad=np.zeros((len(pts),10),complex)
   for p in range(idx.shape[1]):
    pr=np.prod(np.delete(selected,p,axis=2),axis=2)*coeff
    for j in range(10):grad[:,j]+=np.sum(pr[:,idx[:,p]==j],axis=1)
   jacs.append(np.einsum('sj,sr,krj->sk',grad,pts,ds))
 if jac:
  J=np.concatenate(jacs);return np.block([[J.real,-J.imag],[J.imag,J.real]])
 val=np.concatenate(vals);return np.concatenate([val.real,val.imag])
rng=np.random.default_rng(29871);best=100;start=time.time()
x=rng.normal(size=24)*.2
J=funjac(x,True);step=1e-6;Jn=np.stack([(funjac(x+np.eye(24)[i]*step)-funjac(x-np.eye(24)[i]*step))/(2*step) for i in range(24)],axis=1)
print('jacerror',np.max(np.abs(J-Jn)),flush=True)
A=decode(x[:12]+1j*x[12:]);print('qtest',sum(coef*np.prod(A[0,list(m)]) for m,coef in terms[2].items()),flush=True)
for trial in range(2000):
 if trial%20==0:
  O=np.linalg.qr(rng.normal(size=(9,9)))[0]
  R=Ui@O@U
  T=R.T@Toriginal
  Tp,Tr,Tw=T[:3],T[3:6],T[6:]
 scale=[.1,.3,.5,1,2][trial%5]
 x=rng.normal(size=24)*scale
 res=least_squares(funjac,x,jac=lambda x:funjac(x,True),method='lm',max_nfev=1000,ftol=1e-12,xtol=1e-12,gtol=1e-12)
 norm=np.linalg.norm(res.fun)
 if norm<best:
  best=norm;A=decode(res.x[:12]+1j*res.x[12:])
  print('BEST',trial,'norm',norm,'normA',np.linalg.norm(A),'time',time.time()-start,flush=True)
  Path('/tmp/oec/pequalnp-pilot-79/generic_witt_numeric_best.json').write_text(json.dumps({'trial':trial,'norm':norm,'x':list(res.x),'A':[[[float(y.real),float(y.imag)] for y in row] for row in A]},indent=2))
 if norm<1e-10:
  print('FOUND',repr(A),flush=True);break
 if trial%20==0:print('PROGRESS',trial,'time',time.time()-start,flush=True)
