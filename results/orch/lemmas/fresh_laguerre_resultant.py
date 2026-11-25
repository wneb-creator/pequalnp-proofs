"""Seven linearized jets at one isolated Laguerre anchor, then quartic-in-alpha tests."""
import itertools as it,sys,math,time,json
from pathlib import Path
import numpy as np
p=int(sys.argv[1]);roots=[a for a in range(p) if (a**4-16*a**3+72*a*a-96*a+24)%p==0]
la=int(sys.argv[2]) if len(sys.argv)>2 else roots[0];assert la in roots
iv=[0]+[pow(i,-1,p) for i in range(1,p)];ll=(-la)%p
# R_S=z³+q2 z²+q1 z+q0 on the selected branch.
q2=(16-la)%p;q1=(72-la*q2)%p;q0=(96-la*q1)%p;assert la*q0%p==24%p
Rc=np.array([q0,q1,q2,1],dtype=int);D=sum(c*pow(ll,k,p) for k,c in enumerate(Rc))%p
assert D
S3=list(range(3));S4=list(range(4));idx3=list(it.combinations_with_replacement(S3,2));Es=np.zeros((6,3,3),dtype=int)
for k,(i,j) in enumerate(idx3):Es[k,i,j]=Es[k,j,i]=1
P3=np.array(list(it.permutations(S3)),dtype=int);P4=np.array(list(it.permutations(S4)),dtype=int)
J=np.ones((4,4),dtype=int);I3=np.ones((3,3),dtype=int)
def rref(M,dim=None):
 A=np.array(M,dtype=np.int64)%p;pv=[];i=0
 for j in range(A.shape[1] if dim is None else dim):
  nz=np.flatnonzero(A[i:,j])
  if not len(nz):continue
  k=i+int(nz[0]);A[[k,i]]=A[[i,k]];A[i]=A[i]*iv[A[i,j]]%p;cc=A[:,j].copy();cc[i]=0;A=(A-cc[:,None]*A[i])%p;pv.append(j);i+=1
  if i==len(A):break
 return A,pv
def K(S):
 n=[list(set(S3)-{x}) for x in S3]
 return np.array([[S[a,i]*S[b,j]+S[a,j]*S[b,i] for i,j in n] for a,b in n])%p
def abc(S):
 k=K(S);f=int(np.prod(S[np.arange(3),P3],axis=1).sum())%p
 return np.array([f,int(k.sum())%p,int(S.sum())%p])
def Tv(S):
 k=K(S);dk=(K(S+1)-k-2)%p
 return (2*la*k.sum(axis=1)-la*la*dk.sum(axis=1)+2*la**3)%p
def block(a,u,S):
 M=np.empty((4,4),dtype=int);M[0,0]=a;M[1:,0]=M[0,1:]=u;M[1:,1:]=S;return M%p
def first_data(S):
 k=K(S);dk=(K(S+1)-k-2)%p;beta=Tv(S)*iv[D]%p
 # Columns of dR and dT on six physical entries.
 rd=[];td=[]
 for e in Es:
  rr=(abc(S+e)-abc(S-e))*iv[2]%p;rr[0]=int((k*e).sum())%p
  rd.append(rr);td.append((Tv(S+e)-Tv(S-e))*iv[2]%p)
 gd=np.r_[np.array(rd).T,np.array(td).T[:2]];N,pv=rref(np.c_[gd,np.eye(5,dtype=int)],6)
 if len(pv)<5:return None,len(pv)
 free=next(i for i in range(6) if i not in pv);null=np.zeros(6,dtype=int);null[free]=1;null[pv]=-N[:,free];null=np.einsum('n,nij->ij',null,Es)%p
 def lift(vals):
  x=np.zeros(6,dtype=int);x[pv]=N[:,6:]@vals%p;return np.einsum('n,nij->ij',x,Es)%p
 prescribed=[]
 for i in range(2):
  h=beta[i];u=np.array([0,k[i].sum(),dk[i].sum()*iv[2],1])%p;f=(-h*Rc-2*u)%p
  d2=f[3];d1=(f[2]-la*d2)%p;d0=(f[1]-la*d1)%p;assert (f[0]-la*d0)%p==0
  prescribed.append(np.array([d0,d1,d2])%p)
 w=np.array([sum(int(x)*pow(ll,i,p) for i,x in enumerate(g)) for g in prescribed])%p
 k2=(k-la*dk+la*la)%p;cross=(beta[0]*w[1]+beta[1]*w[0]+2*k2[0,1])%p
 bs=[lift(np.r_[prescribed[0],(beta[0]*w[0]+k2[0,0])%p,0]),lift(np.r_[prescribed[1],cross,(beta[1]*w[1]+k2[1,1])%p])]
 ds=[lift(np.array([0,0,0,0,1])),lift(np.array([0,0,0,-1,0]))];A=block(la,[0,0,0],S)
 BB=np.array([block(beta[i],np.eye(3,dtype=int)[i],bs[i]) for i in range(2)])
 DD=np.array([block(0,[0,0,0],q) for q in ds]);E=block(0,[0,0,0],null)
 return (A,BB,DD,E),5
rows=np.arange(4);co2=list(it.combinations(S4,2));co3=list(it.combinations(S4,3))
def polar(A,T,co):
 # T shape (...,4,4), A shape (4,4), vectorize all 24 terms and all parameter samples.
 q=T[...,rows,P4];a=A[rows,P4];ret=np.zeros(q.shape[:-2],dtype=np.int64)
 for slots in co:
  z=np.ones(q.shape[:-1],dtype=np.int64)
  for i in S4:z=z*(q[...,i] if i in slots else a[...,i])%p
  ret+=z.sum(axis=-1)
 return ret%p
def resultant_quad(f,g):
 a,b,c=np.moveaxis(f,-1,0);d,e,h=np.moveaxis(g,-1,0)
 return ((a*h-c*d)**2-(a*e-b*d)*(b*h-c*e))%p
slopes=[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)];alpha=np.arange(5,dtype=np.int64);I3s=np.array([[(i**j)%p for j in range(3)] for i in [-1,0,1]],dtype=int);vv=rref(np.c_[I3s,np.eye(3,dtype=int)],3)[0][:,3:];va=np.array([[pow(i,j,p) for j in range(5)] for i in range(5)]);va=rref(np.c_[va,np.eye(5,dtype=int)],5)[0][:,5:]
def verdict(S,detail=False):
 data,rk=first_data(S)
 if not data:return {'jet_rank':rk}
 A,B,C,E=data;b=np.array(slopes)@B.reshape(2,16)%p;c=np.array(slopes)@C.reshape(2,16)%p
 T=(b[:,None,None,:]+alpha[None,:,None,None]*c[:,None,None,:]+np.array([-1,0,1])[None,None,:,None]*E.reshape(1,1,1,16))%p
 T=T.reshape(len(slopes),5,3,4,4)
 qs=[polar(A,T,co2),polar(J,T,co2),polar((A-la*J)%p,T,co3)]
 polys=[u@vv.T%p for u in qs];rr=[resultant_quad(polys[i],polys[j])@va.T%p for i,j in it.combinations(range(3),2)]
 # Q_AA,Q_JJ quadrics in t and alpha; C_lambda cubic polar is quadratic in these same parameters.
 initial=len(rref(rr[0])[1]);allr=len(rref(np.vstack(rr))[1]);out={'jet_rank':5,'Qresultant_rank':initial,'all_resultant_rank':allr}
 if detail:out.update(leadingQ=polys[0][0,0].tolist(),p=p,root=la,S=S.tolist(),coefficient_rows=[g.tolist() for g in rr])
 return out
if __name__=='__main__':
 if len(roots)==4:
  a=roots[:];a.remove(la);S=np.diag(a);assert (abc(S)==Rc[:3]).all();out=verdict(S,True);print(json.dumps(out));Path('fresh_laguerre_resultant_'+str(p)+'.json').write_text(json.dumps(out))
