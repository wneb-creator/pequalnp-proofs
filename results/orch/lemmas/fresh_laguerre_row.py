"""Single full row, split Laguerre roots, 17-variable affine input with no variable pivots."""
from pathlib import Path
from itertools import permutations,combinations,product
from collections import defaultdict
import sys,re,time
from sympy.polys.rings import ring
from sympy.polys.domains import GF
p=int(sys.argv[1]);colors=list(map(int,sys.argv[2]));mode=sys.argv[3];variant=sys.argv[4] if len(sys.argv)>4 else 'all';jdir=Path('/tmp/oec/pequalnp-pilot-79');st=time.time()
roots=[i for i in range(p) if (i**4-16*i**3+72*i*i-96*i+24)%p==0];assert len(roots)==4 and len(colors)==4
la,*lower=[roots[i] for i in colors];other=roots[:];other.remove(la);den=1
for x in other:den=den*(x-la)%p
assert den;I=range(3);pairs=list(combinations(I,2));vs=['b','c']+[s+n for s in 'BCS' for n in ['0','1','01','02','12']]
R,*V=ring(','.join(vs),GF(p));t=dict(zip(vs,V));zero,one=R.zero,R.one;b,c=V[:2]
def lowsum(key,sm):
 M=[[zero for _ in I] for _ in I]
 for i,j in pairs:M[i][j]=M[j][i]=t[key+str(i)+str(j)]
 M[0][0]=t[key+'0'];M[1][1]=t[key+'1'];M[2][2]=sm-M[0][0]-M[1][1]-2*sum(M[i][j] for i,j in pairs)
 return M
S=lowsum('S',16-la);BS=lowsum('B',-b-2);CS=lowsum('C',-c-2)
def block(q,v,S):return [[q,*v]]+[[v[i],*S[i]] for i in I]
A=block(la*one,[zero]*3,S);J=[[one]*4 for _ in range(4)];B=block(b,[one,zero,zero],BS);C=block(c,[zero,one,zero],CS)
def K(M):
 return [[M[k][r]*M[l][s]+M[k][s]*M[l][r] for j in I for r,s in [[x for x in I if x!=j]]] for i in I for k,l in [[x for x in I if x!=i]]]
def per3(M):return sum(M[0][pi[0]]*M[1][pi[1]]*M[2][pi[2]] for pi in permutations(I))
def det(M):
 return sum((-1)**sum(pi[i]>pi[j] for i,j in combinations(range(len(M)),2))*prodvals([M[i][pi[i]] for i in range(len(M))]) for pi in permutations(range(len(M))))
def prodvals(fs):
 a=one
 for f in fs:a*=f
 return a
ps=[];labels=[]
def push(f,name):
 if not f:return
 f=f.quo_ground(f.LC)
 if f not in ps:labels.append(name);ps.append(f)
ks=K(S);kj=K([[S[i][j]+1 for j in I] for i in I]);lin=[[kj[i][j]-ks[i][j]-2 for j in I] for i in I]
push(sum(map(sum,ks))-(other[0]*other[1]+other[0]*other[2]+other[1]*other[2]),'S rook coefficient 1');push(per3(S)-24*pow(la,-1,p),'S permanent')
for i,d in enumerate([b,c]):push(den*d-2*la*sum(ks[i])+la**2*sum(lin[i])-2*la**3,'diagonal directional derivative '+str(i))
M=[A,J,B,C];forms=defaultdict(lambda:zero)
for pi in permutations(range(4)):
 for picks in product(range(4),repeat=4):
  if max(picks)<2:continue
  order=tuple(sorted(picks));forms[order]+=prodvals([M[j][i][pi[i]] for i,j in enumerate(picks)])
for o,f in sorted(forms.items(),key=lambda u:(sum(x>=2 for x in u[0]),u[0])):push(f,'polar'+str(o))
# Borel evaluation at z=-lambda. At order two this is linear in the lower slopes
# for a fixed anchor and the prescribed top diagonals. At order three it is quadratic.
from math import factorial
for deg in [2,3]:
 for nB in range(deg+1):
  g=zero
  for k in range(5-deg):
   o=tuple([0]*(4-deg-k)+[1]*k+[2]*nB+[3]*(deg-nB))
   g+=pow(-la,k,p)*pow(factorial(k),-1,p)*forms[o]
  push(g,'isolated-root '+str((deg,nB)))
if variant!='norows':
 for i,lr in enumerate(lower,1):
  jj=[k for k in range(4) if k!=i];F=[[m[i][k] for k in jj]+[m[i][i]-lr*ee] for m,ee in zip(M,[1,1,0,0])];push(det(F),'other row Laguerre '+str(i))
if mode=='fiber':
 # User-supplied S entries can instead be inserted as five additional linear equations.
 for k,root in zip(['S0','S1','S01','S02','S12'],map(int,sys.argv[5:])):push(t[k]-root,'fiber '+k)
tag='_'.join(sys.argv[1:]);out=jdir/('fresh_laguerre_row_'+tag+'.msolve')
with out.open('w') as f:
 f.write(','.join(vs)+'\n'+str(p)+'\n'+',\n'.join(re.sub(r'\s*mod\s*'+str(p)+r'\b','',str(g)).replace('**','^').replace(' ','') for g in ps)+'\n')
print('prime',p,'colors',colors,'lambda',la,'weights',[la,*lower],'variables',len(vs),'equations',len(ps),'terms',sum(map(len,ps)),'generation_seconds',time.time()-st)
print('degrees/terms by equation',[(n,max(sum(e) for e in f),len(f)) for n,f in zip(labels,ps)])
