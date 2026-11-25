"""Check diagonal anchor from the Cauchy frame using exact finite-field tensor contractions."""
from pathlib import Path
import sys,json,itertools as it
from math import isqrt
def isprime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def roots(n):return [x for x in range(n) if (((x-16)*x+72)*x*x-96*x+24)%n==0]
for pp in range(7,5500):
 if isprime(pp) and any(i*i%pp==24%pp for i in range(pp)):
  rr=roots(pp)
  if len(rr)==4 and len({(i+j)%pp for i,j in it.combinations(rr,2)})==6:break
else:raise ValueError('no splitting prime')
sys.argv=[sys.argv[0],str(pp),'0']
from fresh_block_moment import *
assert pp==p
A=np.diag(rr);print('prime',p,'roots',rr,flush=True)
bas=np.array([np.diag([pow(int(i),k,p) for i in rr]) for k in range(4)]+[np.array([[0 if i==j else pow((rr[i]+rr[j])%p,k,p) for j in S] for i in S]) for k in range(6)])
Ss=np.array([grad(A+i*J) for i in range(4)]);G=np.einsum('ijk,mjk->im',Ss,bas)%p
gg=np.array([int(i==4) for i in range(10)]);N,ps=rref(np.r_[G,[gg]]);fr=[i for i in range(10) if i not in ps]
assert len(fr)==5,fr
coords=np.zeros((5,10),dtype=int)
for i,j in enumerate(fr):coords[i,j]=1;coords[i,ps]=-N[:5,j]
Ds=np.einsum('ni,ijk->njk',coords,bas)%p
Hs=qnet(A,Ds);pr=lambda x:print(x,flush=True)
out=dict(p=p,roots=rr,pivots=ps,free=fr,G=G.tolist(),coords=(coords%p).tolist(),Q=Hs.tolist())
for Htri in [np.eye(3,dtype=int)[::-1],np.eye(3,dtype=int),np.array([[1,1,1],[1,2,4],[1,3,9]],dtype=int),np.array([[1,1,0],[1,0,1],[1,1,1]],dtype=int)]:
 H0,H1,H2=np.einsum('ij,jab->iab',Htri,Hs)%p;M,pivs=rref(np.c_[H0,np.eye(5,dtype=int)],5)
 if len(pivs)<5:pr('singular H0');continue
 P=M[:,5:]@H1%p;R=M[:,5:]@H2%p;ee=len(rref(P@R-R@P)[1]);pr(['pencil',Htri.tolist(),'commutator_rank',ee,'moment',moment(A,Ds,Hs,Htri,needC=True)])
 L=[H0,H1,H1@P%p,P.T@H1@P%p,H2,H2@P%p,P.T@H2@P%p];T=np.zeros((7,5,35),dtype=int)
 for i in range(5):T[:,i,qcols3[i]]=np.array([qform(a) for a in L])
 M35=T.reshape(35,35);dd=det(M35);pr(['H0det',det(H0),'momentdet',dd])
 if dd:
  out.update(pencil=Htri.tolist(),detH0=det(H0),det35=int(dd),matrix=M35.tolist());break
Path('fresh_diagonal_anchor.json').write_text(json.dumps(out,separators=(',',':')))
