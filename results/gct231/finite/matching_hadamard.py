import sympy as s,itertools,time,json
from pathlib import Path
x,y,z,d,e,f,q,h=s.symbols('x y z d e f q h')
T=s.Matrix([[d+e+f,x,y,z],[x,d-e-f,-z,-y],[y,-z,-d+e-f,-x],[z,-y,-x,-d-e+f]])
p=s.expand(sum(s.prod(1+q*T[i,perm[i]] for i in range(4)) for perm in itertools.permutations(range(4)))-24)
for degree in range(1,5): print('coefficient',degree,s.factor(p.coeff(q,degree)),flush=True)
vec=[x,y,z];ds=[d,e,f];hits=[];counts={}
for perm in itertools.permutations(range(3)):
 for signs in itertools.product([-1,1],repeat=3):
  sub={ds[i]:-2*vec[i]+h*signs[i]*vec[perm[i]] for i in range(3)}
  c3=s.rem(s.expand(p.coeff(q,3).subs(sub)),h*h-3,h)
  if c3==0:
   c4=s.rem(s.expand(p.coeff(q,4).subs(sub)),h*h-3,h)
   hits.append((perm,signs,str(s.factor(c4))))
print('signed_permutation_cubic_hits',hits,flush=True)
