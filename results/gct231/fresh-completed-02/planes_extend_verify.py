import sympy as s
from itertools import permutations,product
x,y,z=s.symbols('x y z')
b=s.symbols('b00 b01 b02 b03 b11 b12 b13 b22 b23 b33')
B=s.zeros(4); k=0
for i in range(4):
 for j in range(i,4):B[i,j]=B[j,i]=b[k];k+=1
perms=list(permutations(range(4)))
rows=[x,y,-x-y]
seen=set()
for perm in permutations(range(3)):
 for signs in product([1,-1],repeat=3):
  if s.prod(signs)!=1:continue
  dif=[signs[i]*rows[perm[i]] for i in range(3)]
  a,bb,c=[(rows[i]+dif[i])/2 for i in range(3)]
  f,e,d=[(rows[i]-dif[i])/2 for i in range(3)]
  T=s.Matrix([[0,a,bb,c],[a,0,d,e],[bb,d,0,f],[c,e,f,0]])
  # classify plane canonically in edge coefficient RREF
  coeff=s.Matrix([[s.expand(T[i,j]).coeff(v) for i in range(4) for j in range(i,4)] for v in [x,y]])
  key=tuple(coeff.rref()[0]);
  if key in seen:continue
  seen.add(key)
  M=s.ones(4)+T+z*B
  fexpr=s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in perms)-24)
  lin=s.Poly(s.expand(fexpr).coeff(z,1),x,y)
  sol=s.linsolve(lin.coeffs(),b)
  bt=next(iter(sol));sub=dict(zip(b,bt))
  free=set().union(*(t.free_symbols for t in bt))
  rest=s.Poly(s.expand(fexpr.subs(sub)),x,y,z)
  cons=list(dict.fromkeys(s.factor(c) for c in rest.coeffs()))
  fv=sorted(free,key=str)
  gro=s.groebner(cons,*fv,order='grevlex',domain=s.QQ)
  annih=coeff.nullspace()
  checks=[]
  for ell in annih:
   value=s.factor(sum(ell[i]*bt[i] for i in range(10)))
   if value==0:continue
   power=next((j for j in range(1,9) if gro.reduce(s.expand(value**j))[1]==0),None)
   checks.append((str(value),power))
  assert all(j is not None for _,j in checks)
  print('CASE',perm,signs,'dim',len(free),'membership_powers',checks,'PASS',flush=True)
