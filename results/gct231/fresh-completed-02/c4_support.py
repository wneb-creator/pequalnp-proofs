import sympy as s,itertools,json,time,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
v=s.symbols('v:7');a,b,c,p,q,r,z=v
T=s.Matrix([[a,p,0,z],[p,b,q,0],[0,q,c,r],[z,0,r,-a-b-c-2*(p+q+r+z)]])
h=s.symbols('h');M=s.ones(4)+h*T
poly=s.Poly(s.expand(sum(s.prod(M[i,pm[i]] for i in range(4)) for pm in itertools.permutations(range(4)))-24),h)
assert poly.nth(1)==0
Q=s.hessian(poly.nth(2),v)/2
print('Q',Q,'det',Q.det(),flush=True)
print('quadratic',s.factor(poly.nth(2)),flush=True)
print('cubic',s.factor(poly.nth(3)),flush=True)
print('quartic',s.factor(poly.nth(4)),flush=True)
dump={'variables':list(map(str,v)),'matrix':[[str(T[i,j]) for j in range(4)] for i in range(4)],'homogeneous':{str(k):str(poly.nth(k)) for k in [2,3,4]}}
(base/'c4-support-homogeneous.json').write_text(json.dumps(dump,indent=2))
