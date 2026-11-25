"""Compare the six-variable chart equations with an independent permutation expansion."""
from pathlib import Path
import itertools as it,random,math,json,hashlib
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
job=Path('/tmp/oec/pequalnp-pilot-79');file=job/'fresh_top_allzero_0.msolve';lines=file.read_text().strip().splitlines();assert lines[:2]==['a,b,c,l,m,n,h','0'];rr,*xx=ring('x,y,z',QQ);h=2*3 # symbolic sqrt24 via pairs below
import sympy as s
h=s.sqrt(24);vs=s.symbols('a b c l m n h');forms=[s.sympify(q.rstrip(',').replace('^','**')) for q in lines[2:]];random.seed(264859)
for trial in range(6):
 av=[random.randint(-4,4) for _ in range(3)];l,m,n=[random.randint(-4,4) for _ in range(3)];tk=[random.randint(-3,3) for _ in range(3)];xx,yy,zz=tk;S=[[0,l,m],[-l,0,n],[-m,-n,0]];w=s.symbols('w');ell=sum(i*j for i,j in zip(av,tk));cc=[16*av[i]-2*h-2*sum(av)*av[i]-2*sum(S[j][i] for j in range(3)) for i in range(3)];bv=[av[i]*ell+sum(S[i][j]*tk[j] for j in range(3)) for i in range(3)];C=s.Matrix(3,3,lambda i,j:cc[i]*tk[i]/h if i==j else bv[3-i-j]/h);N=s.zeros(4);N[0,1:]=s.Matrix(tk).T;N[1:,0]=s.Matrix(tk);N[1:,1:]=C;M=s.ones(4)+w*N;F=s.Poly(s.expand(sum(s.prod(M[i,j] for i,j in enumerate(pm)) for pm in it.permutations(range(4)))-24*(1+w*ell/h)**4),w);data=[v.subs(dict(zip(vs,av+[l,m,n,h]))) for v in forms];assert data[0]==0
 for d,first,count in [(2,1,6),(3,7,10),(1,17,3)]:
  vals=data[first:first+count];ex=[v for v in it.product(range(d+1),repeat=3) if sum(v)==d];v=sum(co*math.prod(n**e for n,e in zip(tk,alpha)) for co,alpha in zip(vals,ex));realdeg=4 if d==1 else d;tgt=F.nth(realdeg)*h**(2 if d==1 else realdeg);rhs=v*math.prod(tk) if d==1 else v;assert s.expand(tgt-rhs)==0,(trial,d,tgt,rhs)
print('6 exact algebraic evaluations match full 24-permutation target expansion; input sha256',hashlib.sha256(file.read_bytes()).hexdigest())
