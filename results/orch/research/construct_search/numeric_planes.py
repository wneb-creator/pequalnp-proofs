import itertools
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import least_squares

job=Path('/tmp/oec/pequalnp-pilot-78/construct_search')
Q=np.array([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],float)/2
S=np.zeros((6,4,4));S[0,1,1]=S[1,2,2]=S[2,3,3]=1
for k,(i,j) in enumerate([(1,2),(1,3),(2,3)],3):S[k,i,j]=S[k,j,i]=1/np.sqrt(2)
D=np.sqrt(6)*np.einsum('ij,mjk,kl->mil',Q,S,Q)
F=np.zeros((3,4,4))
for a in range(3):F[a,0,a+1]=F[a,a+1,0]=1
F=np.einsum('ij,ajk,kl->ail',Q,F,Q)
perms=np.array(list(itertools.permutations(range(4))))
piv=list(zip(*np.triu_indices(3)))

def interpolation(d):
    mons=[(a,b,d-a-b) for a in range(d+1) for b in range(d-a+1)]
    points=np.array(mons,float)/d
    matrix=np.array([[np.prod(p**np.array(m)) for m in mons] for p in points])
    return points,np.linalg.inv(matrix)

pts3,I3=interpolation(3);pts4,I4=interpolation(4)
pts=np.concatenate([pts3,pts4]);n3=len(pts3)
DG=np.stack([D[:,i,perms[:,i]] for i in range(4)],axis=2)

def evaluate(X,derivative=False):
    bases=F+np.einsum('ma,mij->aij',X,D)
    T=np.einsum('sa,aij->sij',pts,bases)
    W=np.stack([T[:,i,perms[:,i]] for i in range(4)],axis=2)
    c4=np.prod(W,axis=2).sum(axis=1)
    c3=sum(np.prod(W[:,:,[j for j in range(4) if j!=i]],axis=2) for i in range(4)).sum(axis=1)
    q=X.T@X-np.eye(3)
    val=np.concatenate([np.array([q[i,j] for i,j in piv]),I3@c3[:n3]/12,I4@c4[n3:]/6])
    if not derivative:return val
    G3=np.zeros((len(pts),6),complex);G4=np.zeros_like(G3)
    for r in range(4):
        others=[i for i in range(4) if i!=r]
        h4=np.prod(W[:,:,others],axis=2)
        h3=sum(W[:,:,i]*W[:,:,j] for i,j in itertools.combinations(others,2))
        G3+=np.einsum('sp,mp->sm',h3,DG[:,:,r])
        G4+=np.einsum('sp,mp->sm',h4,DG[:,:,r])
    J3=np.einsum('sm,sa->sma',G3,pts).reshape(len(pts),18)
    J4=np.einsum('sm,sa->sma',G4,pts).reshape(len(pts),18)
    Jq=np.zeros((6,6,3),complex)
    for k,(i,j) in enumerate(piv):
        Jq[k,:,i]+=X[:,j]
        Jq[k,:,j]+=X[:,i]
    J=np.concatenate([Jq.reshape(6,18),I3@J3[:n3]/12,I4@J4[n3:]/6])
    return val,J

def unpack(x):return (x[:18]+1j*x[18:]).reshape(6,3)
def fun(x):
    v=evaluate(unpack(x))
    return np.r_[v.real,v.imag]
def jac(x):
    v,J=evaluate(unpack(x),True)
    return np.block([[J.real,-J.imag],[J.imag,J.real]])

rng=np.random.default_rng(231)
x=rng.normal(size=36)*.2
v,J=evaluate(unpack(x),True)
for k in [0,5,17]:
    h=np.zeros(36);h[k]=1e-6
    err=np.max(abs((fun(x+h)-fun(x-h))/(2e-6)-jac(x)[:,k]))
    print('JAC_CHECK',k,err,flush=True)
best=1e100;started=time.time()
for trial in range(150):
    X=np.linalg.qr(rng.normal(size=(6,3)))[0].astype(complex)
    if trial%3:X+=1j*rng.normal(size=(6,3))*(.2 if trial%3==1 else 1)
    init=np.r_[X.real.ravel(),X.imag.ravel()]
    result=least_squares(fun,init,jac=jac,max_nfev=1200,ftol=1e-12,gtol=1e-12,xtol=1e-12)
    err=np.max(np.abs(fun(result.x)))
    X=unpack(result.x)
    print('TRIAL',trial,'ERR',err,'NORM',np.linalg.norm(X),'NFEV',result.nfev,'SECONDS',time.time()-started,flush=True)
    if err<best:
        best=err
        (job/'numeric-best.json').write_text(json.dumps({'trial':trial,'error':err,'real':X.real.tolist(),'imag':X.imag.tolist()}))
    if err<1e-8:
        print('FOUND',X,flush=True)
        break
