from pathlib import Path
from itertools import permutations,combinations
import re,sys,time
from sympy.polys.rings import ring
from sympy.polys.domains import GF,QQ
p=int(sys.argv[1]);lt=int(sys.argv[2]);tag=sys.argv[3];st=time.time()
names=['d0','d1','e01','e02','e12']+([] if p else ['la']);R,*v=ring(','.join(names),GF(p) if p else QQ)
a,b,x,y,z=v[:5];la=lt if p else v[-1];c=16-la-2*(x+y+z)-a-b;S=[[a,x,y],[x,b,z],[y,z,c]]
I=list(range(3));n=[list(set(I)-{i}) for i in I];K=[[S[r][k]*S[s][m]+S[r][m]*S[s][k] for k,m in n] for r,s in n]
q=sum(map(sum,K));pm=sum(S[0][t[0]]*S[1][t[1]]*S[2][t[2]] for t in permutations(I));data=[q,pm]+[sum(K[i])+la*sum(S[i]) for i in [0,1]]
funs=[[g.diff(v[j]) for j in range(5)] for g in data]
def prod(xs):
 a=R.one
 for x in xs:a*=x
 return a
def detcols(ids):
 return sum((-1)**sum(pm[i]>pm[j] for i,j in combinations(range(4),2))*prod(funs[k][ids[pm[k]]] for k in range(4)) for pm in permutations(range(4)))
eq=[q-72+la*(16-la),pm-96+la*(72-la*(16-la))]
if not p:eq.insert(0,la**4-16*la**3+72*la*la-96*la+24)
ms=[detcols(ind) for ind in combinations(range(5),4)]
if tag=='all':eq+=ms
elif tag.startswith('m'):eq+=[ms[int(tag[1:])]]
else:raise ValueError('unknown mode')
out=Path('fresh_laguerre_jac_'+str(p)+'_'+str(lt)+'_'+tag+'.msolve')
with out.open('w') as f:
 f.write(','.join(names)+'\n'+str(p)+'\n'+',\n'.join(re.sub(r'\s*mod\s*'+str(p)+r'\b','',str(g)).replace('**','^').replace(' ','') for g in eq)+'\n')
print('terms',list(map(len,eq)),'generation',time.time()-st)
