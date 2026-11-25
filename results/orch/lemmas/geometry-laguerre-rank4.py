from pathlib import Path
from itertools import permutations,combinations
import resource,sys,json,re,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(115,120))
from sympy.polys.rings import ring
from sympy.polys.domains import GF
start=time.time();p=int(sys.argv[1]);la=int(sys.argv[2]);assert (la**4-16*la**3+72*la**2-96*la+24)%p==0
R,*v=ring('d0,d1,e01,e02,e12',GF(p));a,b,x,y,z=v;c=16-la-2*(x+y+z)-a-b
S=[[a,x,y],[x,b,z],[y,z,c]];idx=list(combinations(range(3),2));phys=list(combinations(range(3),1))
phys=list(combinations(range(3),2))
phys=[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
comp=[[j for j in range(3) if i!=j] for i in range(3)]
def K(S):return [[S[rr[0]][cc[0]]*S[rr[1]][cc[1]]+S[rr[0]][cc[1]]*S[rr[1]][cc[0]] for cc in comp] for rr in comp]
def add(S,E,m=1):return [[S[i][j]+m*E[i][j] for j in range(3)] for i in range(3)]
def pm(S):return sum((S[0][q[0]]*S[1][q[1]]*S[2][q[2]] for q in permutations(range(3))),R.zero)
def ss(S):return sum((sum(row,R.zero) for row in S),R.zero)
ones=[[R.one for j in range(3)]for i in range(3)]
def TV(S):
 k=K(S);kp=K(add(S,ones));dk=[[kp[i][j]-k[i][j]-2 for j in range(3)]for i in range(3)]
 return [2*la*sum(k[i],R.zero)-la**2*sum(dk[i],R.zero)+2*la**3 for i in range(3)]
k=K(S);dk=[[K(add(S,ones))[i][j]-k[i][j]-2 for j in range(3)]for i in range(3)]
Rc=[(96-la*(72-la*(16-la)))%p,(72-la*(16-la))%p,(16-la)%p,1]
D=sum(Rc[i]*pow(-la,i,p) for i in range(4))%p;assert D
beta=[g*pow(D,-1,p) for g in TV(S)]
M=[[]for _ in range(5)]
for i,j in phys:
 E=[[R.zero for _ in range(3)]for _ in range(3)];E[i][j]=E[j][i]=R.one
 sp,sm=add(S,E),add(S,E,-1)
 col=[sum((k[ii][jj]*E[ii][jj] for ii in range(3) for jj in range(3)),R.zero),(ss(K(sp))-ss(K(sm)))*pow(2,-1,p),ss(E)]
 col += [(TV(sp)[ii]-TV(sm)[ii])*pow(2,-1,p) for ii in range(2)]
 for row,g in zip(M,col):row.append(g)
prs=[]
for i in range(2):
 u=[R.zero,sum(k[i],R.zero),sum(dk[i],R.zero)*pow(2,-1,p),R.one]
 f=[-beta[i]*Rc[j]-2*u[j] for j in range(4)]
 d2=f[3];d1=f[2]-la*d2;d0=f[1]-la*d1
 assert not (f[0]-la*d0)
 prs.append([d0,d1,d2])
wv=[sum((prs[k][i]*pow(-la,i,p) for i in range(3)),R.zero)for k in range(2)]
k2=[[k[i][j]-la*dk[i][j]+la**2 for j in range(3)]for i in range(3)]
cross=beta[0]*wv[1]+beta[1]*wv[0]+2*k2[0][1]
UB=prs[0]+[beta[0]*wv[0]+k2[0][0],R.zero]
UC=prs[1]+[cross,beta[1]*wv[1]+k2[1][1]]
def det(A):
 n=len(A);out=R.zero
 for t in permutations(range(n)):
  term=R.one
  for i in range(n):term*=A[i][t[i]]
  out+=(-1)**sum(t[i]>t[j] for i,j in combinations(range(n),2))*term
 return out
# The original full-rank-failure variety; all five maximal minors of the trace-eliminated Jacobian.
q=ss(k);per=pm(S)
data=[q,per]+[sum(k[i],R.zero)+la*sum(S[i],R.zero)for i in range(2)]
jac=[[g.diff(v[j])for j in range(5)]for g in data]
base=[q-Rc[1],per-Rc[0]]+[det([[jac[i][j]for j in ids]for i in range(4)])for ids in combinations(range(5),4)]
compat=[]
for cols in combinations(range(6),4):
 w=[(-1)**i*det([[M[j][c]for c in cols]for j in range(5)if j!=i])for i in range(5)]
 compa=w[3]*sum((w[i]*UB[i]for i in range(5)),R.zero)+w[4]*sum((w[i]*UC[i]for i in range(5)),R.zero)
 if compa:compat.append(compa)
 print('columns',cols,'minor_terms',[len(g)for g in w],'compat_terms',len(compa),flush=True)
# Rank<=3 of physical M corresponds rank<=2 of the trace-eliminated four by five Jacobian.
low=[det([[jac[i][j]for j in cs]for i in rs])for rs in combinations(range(4),3)for cs in combinations(range(5),3)]
for tag,eq in [('compat',base+compat),('rank3',base+low)]:
 name=f'geometry-laguerre-rank4-{p}-{la}-{tag}.msolve'
 Path(name).write_text(','.join(str(t)for t in v)+'\n'+str(p)+'\n'+',\n'.join(re.sub(r'\s*mod\s*'+str(p)+r'\b','',str(g)).replace('**','^').replace(' ','')for g in eq if g)+'\n')
 print('saved',name,'equations',len(eq),'terms',sum(map(len,eq)),flush=True)
print('seconds',time.time()-start,flush=True)
