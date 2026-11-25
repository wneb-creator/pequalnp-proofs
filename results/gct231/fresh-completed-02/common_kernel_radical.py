import sympy as s,itertools,json,time
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
a,b,c,h,x,y=s.symbols('a b c h x y')
w=s.Matrix([a,b,c,1-a-b-c]);delta=w[0]-w[3]
u=s.Matrix([(w[3]-w[1])*x+(w[3]-w[2])*y,delta*x,delta*y,-(w[0]-w[1])*x-(w[0]-w[2])*y])
assert s.expand(sum(u))==0 and s.expand((w.T*u)[0])==0
T=w*u.T+u*w.T
rr,*gg=ring('a,b,c,x,y',QQ)
TT=[[rr.from_expr(s.expand(T[i,j])) for j in range(4)] for i in range(4)]
equations=[s.expand((w.T*w)[0]-1),h*delta-1]
for k in [1,2,3,4]:
 total=rr.zero
 for p in itertools.permutations(range(4)):
  for inds in itertools.combinations(range(4),k):
   term=rr.one
   for i in inds:term*=TT[i][p[i]]
   total+=term
 groups={}
 for mon,coeff in total.items():
  xy=tuple(mon[-2:]);groups.setdefault(xy,0)
  groups[xy]+=s.Rational(coeff.numerator,coeff.denominator)*a**mon[0]*b**mon[1]*c**mon[2]
 polys=[s.factor(v) for v in groups.values() if v!=0]
 print('degree',k,'coefficients',polys,flush=True)
 if k>=3:equations.extend(polys)
print('starting Groebner',len(equations),flush=True)
start=time.monotonic()
G=s.groebner(equations,h,a,b,c,domain=s.QQ,order='grevlex')
print('basis',list(G),flush=True)
print('seconds',time.monotonic()-start,flush=True)
L=G.fglm('lex') if G.is_zero_dimensional else G
print('lex',list(L),flush=True)
