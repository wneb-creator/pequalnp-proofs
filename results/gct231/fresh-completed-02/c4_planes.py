import sympy as s,itertools
a,b,c,x,y,z=s.symbols('a b c x y z')
N=s.Matrix([[-c,b,-a,-b],[b,c,-b,a],[-a,-b,-c,b],[-b,a,b,c]])
def charmat(u,v,sign):
 j=sign*s.I
 return s.Matrix([[j*v,-u,0,j*u],[-u,-v,-j*u,0],[0,-j*u,-j*v,u],[j*u,0,u,v]])
up=[(1,0)]+[(sign*(1+s.I)/(2*s.sqrt(2)),1) for sign in [1,-1]]
down=[(1,0)]+[(sign*(1-s.I)/(2*s.sqrt(2)),1) for sign in [1,-1]]
def perm(T):return s.expand(sum(s.prod(T[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))
for i,uu in enumerate(up):
 for j,vv in enumerate(down):
  U=charmat(*uu,1);V=charmat(*vv,-1)
  pair=s.Poly(perm(s.ones(4)+y*U+z*V)-24,y,z)
  paircs=[s.simplify(q) for q in pair.coeffs() if s.simplify(q)!=0]
  print('PAIR',i,j,'pair coefficients',paircs,flush=True)
  if paircs:continue
  allcs=s.Poly(perm(s.ones(4)+x*N+y*U+z*V)-24,x,y,z).coeffs()
  linear=[q for q in allcs if s.Poly(q,a,b,c).total_degree()==1]
  sols=s.linsolve(linear,(a,b,c));print('linear N solutions',sols,flush=True)
  sub=dict(zip((a,b,c),next(iter(sols))))
  rest=[s.simplify(q.subs(sub)) for q in allcs]
  print('remaining',list(dict.fromkeys(q for q in rest if q!=0)),flush=True)
