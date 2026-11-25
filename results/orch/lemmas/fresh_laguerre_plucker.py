"""Division-free circuit for the pivot-free common-direction resultant on a full row."""
from fresh_block_moment_circuit import Circuit,Scalar
from itertools import combinations,permutations,product
from functools import lru_cache
import json,sys,time
from pathlib import Path
I=range(3);F=range(4);pairs=list(combinations(I,2))
def kcof(S):return [[S[k][i]*S[l][j]+S[k][j]*S[l][i] for h in I for i,j in [[e for e in I if e!=h]]] for m in I for k,l in [[e for e in I if e!=m]]]
def perm3(S):return sum(S[0][x[0]]*S[1][x[1]]*S[2][x[2]] for x in permutations(I))
def block(a,v,S):return [[a]+list(v)]+[[v[i]]+list(S[i]) for i in I]
def vmul(row,mat):return [sum(row[k]*mat[k][j] for k in range(len(row))) for j in range(len(mat[0]))]
def addM(A,B,c=1):return [[u+c*v for u,v in zip(ar,br)] for ar,br in zip(A,B)]
def polar(A,T,d):
 s=0
 for pi in permutations(F):
  for ix in combinations(F,d):
   a=1
   for i in F:a*=T[i][pi[i]] if i in ix else A[i][pi[i]]
   s+=a
 return s
def build(p,la):
 C=Circuit();v=C.var;z=C.const(0);one=C.const(1);iv=lambda t:pow(int(t)%p,-1,p)
 a,b,x,y,zz=[v(t) for t in ['a','b','x','y','z']];alpha=v('alpha');u=v('u');vv=v('v')
 c=16-la-2*(x+y+zz)-a-b;S=[[a,x,y],[x,b,zz],[y,zz,c]];JS=[[one]*3 for i in I];A=block(la*one,[z]*3,S);J=[[one]*4 for i in F]
 q2=(16-la)%p;q1=(72-la*q2)%p;q0=(96-la*q1)%p;ll=(-la)%p;rc=[q0,q1,q2,1];D=sum(e*pow(ll,k,p) for k,e in enumerate(rc))%p
 E=[]
 ij=list((i,j) for i in I for j in range(i,3))
 for i,j in ij:
  m=[[z]*3 for t in I];m[i][j]=m[j][i]=one;E.append(m)
 K=kcof(S);Kj=kcof(addM(S,JS));Kd=[[Kj[i][j]-K[i][j]-2 for j in I] for i in I]
 def Tv(S):
  k=kcof(S);j=kcof(addM(S,JS))
  return [2*la*sum(k[i])-la*la*sum(j[i][h]-k[i][h]-2 for h in I)+2*la**3 for i in I]
 t0=Tv(S);beta=[h*iv(D) for h in t0]
 rows=[[] for i in range(5)]
 for e in E:
  Sp,Sm=addM(S,e),addM(S,e,-1);kp,km=kcof(Sp),kcof(Sm);tp,tm=Tv(Sp),Tv(Sm)
  ds=[sum(K[i][j]*e[i][j] for i,j in product(I,repeat=2)),(sum(map(sum,kp))-sum(map(sum,km)))*iv(2),sum(map(sum,e)),(tp[0]-tm[0])*iv(2),(tp[1]-tm[1])*iv(2)]
  for i,x0 in enumerate(ds):rows[i].append(x0)
 def first(i):
  h=beta[i];n0=-h*q0;n1=-h*q1-2*sum(K[i]);n2=-h*q2-sum(Kd[i]);n3=-h-2
  d2=n3;d1=n2-la*d2;d0=n1-la*d1;return [d0,d1,d2]
 sB,sC=first(0),first(1);wb=sum(vv0*pow(ll,k,p) for k,vv0 in enumerate(sB));wc=sum(vv0*pow(ll,k,p) for k,vv0 in enumerate(sC));k2=[[K[i][j]-la*Kd[i][j]+la*la for j in I] for i in I]
 tB=sB+[beta[0]*wb+k2[0][0],alpha];tC=sC+[beta[0]*wc+beta[1]*wb+2*k2[0][1]-alpha,beta[1]*wc+k2[1][1]]
 H=[[-(u*tB[i]+vv*tC[i])]+rows[i] for i in range(5)]
 @lru_cache(None)
 def dm(cols):
  if not cols:return one
  r=len(cols)-1
  return sum(((-1)**(r+k))*H[r][j]*dm(cols[:k]+cols[k+1:]) for k,j in enumerate(cols))
 P=[[z for j in range(7)] for i in range(7)]
 for i,j in combinations(range(7),2):
  P[i][j]=(-1)**(i+j+1)*dm(tuple(k for k in range(7) if k not in [i,j]));P[j][i]=-P[i][j]
 BP=block(u*beta[0]+vv*beta[1],[u,vv,z],[[z]*3 for i in I]);bs=[BP]+[block(z,[z]*3,e) for e in E]
 def qmatrix(Fn):
  G=[[z]*7 for i in range(7)]
  for i in range(7):G[i][i]=Fn(bs[i])
  for j in range(7):
   for i in range(j):G[i][j]=G[j][i]=(Fn(addM(bs[i],bs[j]))-G[i][i]-G[j][j])*iv(2)
  return G
 Q=[qmatrix(lambda T:polar(A,T,2)),qmatrix(lambda T:polar(J,T,2))]
 Al=addM(A,J,-la);base=polar(Al,BP,3)
 # Cubic polar C_lambda(z,U)/z is a homogeneous quadratic (no all-lower U^3 term).
 G=[[z]*7 for i in range(7)];G[0][0]=base
 def gr(L):return (polar(Al,addM(BP,L),3)+polar(Al,addM(BP,L,-1),3))*iv(2)-base
 for i in range(1,7):
  a1=polar(Al,addM(BP,bs[i]),3);a2=polar(Al,addM(BP,bs[i],-1),3)
  G[0][i]=G[i][0]=(a1-a2)*iv(4);G[i][i]=(a1+a2)*iv(2)-base
 for i,j in combinations(range(1,7),2):G[i][j]=G[j][i]=(gr(addM(bs[i],bs[j]))-G[i][i]-G[j][j])*iv(2)
 Q.append(G)
 ap=[[vmul(r,P) for r in m] for m in Q]
 def tr(i,j):return sum(ap[i][k][l]*ap[j][l][k] for k,l in product(range(7),repeat=2))
 diag=[tr(i,i) for i in I];out=[tr(i,j)**2-diag[i]*diag[j] for i,j in pairs]
 return {'nodes':C.nodes,'out':[s.i for s in out],'minor':[P[0][k].i for k in range(1,7)],'p':p,'la':la}
if __name__=='__main__':
 p,la=map(int,sys.argv[1:3]);t=time.time();c=build(p,la);out=Path('fresh_laguerre_plucker_'+str(p)+'.json');out.write_text(json.dumps(c,separators=(',',':')));print('nodes',len(c['nodes']),'bytes',out.stat().st_size,'time',time.time()-t)
