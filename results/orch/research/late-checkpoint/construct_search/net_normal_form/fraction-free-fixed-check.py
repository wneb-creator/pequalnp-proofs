from pathlib import Path
import sympy as s,itertools,json,sys
job=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form')
a,b,c,d,e,f=map(s.Integer,[1,5,-12,2,5,-1] if len(sys.argv)>1 else [-1,-5,12,-2,-5,1]);hs=[a,b,c,d,e,f];edges=list(itertools.combinations(range(4),2));H=s.zeros(4)
for (i,j),v in zip(edges,hs):H[i,j]=H[j,i]=v
rows=list(H*s.ones(4,1));tau=[d*e*f,b*c*f,a*c*e,a*b*d];E=a*b*c*d*e*f;A=a*f;B=b*e;C=c*d;u,v,w=a+f,b+e,c+d;p,q,r=a-f,b-e,c-d;delta=u*(B-C)+v*(C-A)+w*(A-B)
x,y,k,l,m=s.symbols('s t k l m');zz=l*x+m*y;D=s.Matrix([a*c*x+zz,a*e*y+zz,-d*f*x-b*f*y+zz,zz]);Amat=s.zeros(4)
for i in range(4):
 Amat[i,i]=rows[i]**2
 for j in range(i+1,4):
  ii,jj=[v for v in range(4) if v not in [i,j]];Amat[i,j]=Amat[j,i]=rows[i]*rows[j]+H[ii,jj]**2/2
hh=s.Matrix([-rows[i]**2/2+sum(H[j,kk]**2 for j,kk in edges if i not in [j,kk])/4 for i in range(4)])
assert sum(hh)==0
Cmat=-Amat/2+(s.ones(4,1)*hh.T-hh*s.ones(1,4))/4
raw=s.diag(*[E/t for t in tau])*Cmat*D
nu=raw-s.ones(4,1)*sum(raw)/4
K=s.zeros(4)
for i,j in edges:
 kk,ll=[v for v in range(4) if v not in [i,j]];pm=[i,j,kk,ll];sign=(-1)**sum(pm[i]>pm[j] for i in range(4) for j in range(i+1,4));K[i,j]=sign*tau[j]*(tau[kk]-tau[ll]);K[j,i]=-sign*tau[i]*(tau[kk]-tau[ll])
nu=nu+k*K*D
mu=s.Matrix([(nu[2]+nu[3])/2,(nu[1]+nu[3])/2,(nu[1]+nu[2])/2])
ER=E*sum(rows[i]*D[i] for i in range(4))/2;EG=-E*sum(D)/2-p*mu[0]-q*mu[1]-r*mu[2]
la=-(v-w)*ER+(B-C)*EG;lb=(u-w)*ER-(A-C)*EG;lc=-la-lb;lam=[la,lb,lc]
off=[a*(la+delta*mu[0]),b*(lb+delta*mu[1]),c*(lc+delta*mu[2]),d*(lc-delta*mu[2]),e*(lb-delta*mu[1]),f*(la-delta*mu[0])]
W=s.diag(*[E*delta*z for z in D])
for (i,j),z in zip(edges,off):W[i,j]=W[j,i]=s.expand(z)
assert s.expand(sum(W))==0
rho=[sum(W[i,j] for j in range(4)) for i in range(4)]
qh=s.expand(-4*sum(rows[i]*rho[i] for i in range(4))+4*sum(H[i,j]*W[i,j] for i,j in edges))
assert qh==0
for point in [(0,0,0),(1,2,-1),(-2,1,3)]:
 WW=W.subs(dict(zip((k,l,m),point)));U,Z=s.symbols('U Z');P=s.Poly(s.expand(sum(s.prod(1+U*H[i,j]+Z*WW[i,j] for i,j in enumerate(pm)) for pm in itertools.permutations(range(4)))-24),U,Z,x,y)
 for (uu,zz,ss,tt),coef in P.terms():
  if zz==1 or (uu==2 and zz==2):assert coef==0
print('FRACTION_FREE_FIXED_CHECK_PASS',flush=True)
print('E',E,'DELTA',delta,'CHECKED_PARAMETER_POINTS',3,flush=True)
print('W_COEFFICIENT_MAX',max(len(str(z)) for z in W),flush=True)
