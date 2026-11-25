import itertools as it,time,sys
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ,GF
p=int(sys.argv[1]);base=Path('/tmp/oec/pequalnp-pilot-79');st=time.time();names='x y z a b c l m n'+(' h' if not p else '');R,*V=ring(names.replace(' ',','),QQ if not p else GF(p));t=V[:3];a=V[3:6];l,m,n=V[6:9];h=V[9] if not p else next(i for i in range(p) if i*i%p==24%p);S=range(3);zero=R.zero;sk=[[zero,l,m],[-l,zero,n],[-m,-n,zero]];ell=sum(a[i]*t[i] for i in S);ee=sum(t);cc=[16*a[i]-2*h-2*sum(a)*a[i]-2*sum(sk[j][i] for j in S) for i in S];b=[a[i]*ell+sum(sk[i][j]*t[j] for j in S) for i in S];C={(i,j):cc[i]*t[i] if i==j else b[3-i-j] for i,j in it.product(S,repeat=2)};K={};K1={}
for i,j in it.product(S,repeat=2):
 g,q=[x for x in S if x!=i];b1,f=[x for x in S if x!=j];K[i,j]=C[g,b1]*C[q,f]+C[g,f]*C[q,b1];K1[i,j]=C[g,b1]+C[g,f]+C[q,b1]+C[q,f]
fs=[2*sum(K.values())+2*h*sum(K1[i,j]*t[j] for i,j in K)+48*ee**2-144*ell**2,sum(C[0,q[0]]*C[1,q[1]]*C[2,q[2]] for q in it.permutations(S))+2*h*sum(K[i,j]*t[j] for i,j in K)+24*sum(t[i]*K1[i,j]*t[j] for i,j in K)-96*ell**3,sum(cc[(i+1)%3]*cc[(i+2)%3]*t[i]+2*cc[i]*b[i] for i in S)];R2,*v2=ring(','.join(names.split()[3:]),QQ if not p else GF(p));eq=[]
if not p:eq.append(v2[-1]**2-24)
for z in fs:
 polys={}
 for ex,co in z.items():
  e=ex[:3];v=ex[3:];f=polys.setdefault(e,R2.zero);f[v]=co
 for e,f in sorted(polys.items()):eq.append(f)
with (base/f'fresh_top_allzero_{p}.msolve').open('w') as fp:
 fp.write(','.join(names.split()[3:])+'\n'+str(p)+'\n');fp.write(',\n'.join(str(f).split('SymmetricModularIntegerMod')[0].replace('**','^').replace(' ','').replace('mod97','') for f in eq)+'\n')
print('eq',len(eq),'terms',sum(len(f) for f in eq),'secs',time.time()-st)
