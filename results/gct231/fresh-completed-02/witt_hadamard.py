"""A rational open Witt chart for the full GCT-231 tangent quadratic.

The chart normalizes the E-coordinate block to I3. It is not a covering by
itself. Every emitted identity and coefficient is over Q.
"""
import sympy as s
import itertools,json,time
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
raw=[]
for i in range(1,4):
 m=s.zeros(4);m[i,i]=1;raw.append(H*m*H)
for i,j in [(2,3),(1,3),(1,2)]:
 m=s.zeros(4);m[i,j]=m[j,i]=1;raw.append(H*m*H)
for i in range(1,4):
 m=s.zeros(4);m[0,i]=m[i,0]=1;raw.append(H*m*H)
G=s.diag(1,1,1,2,2,2,-6,-6,-6)
one=s.ones(4,1)
assert s.Matrix(9,9,lambda i,j:s.trace(raw[i]*raw[j])-2*((raw[i]*one).T*(raw[j]*one))[0])==G
E=s.Matrix.vstack(2*s.eye(3),s.eye(3),s.eye(3))
F=s.Matrix.vstack(2*s.eye(3),s.eye(3),-s.eye(3))/12
R=s.Matrix.vstack(s.eye(3),-s.eye(3),s.zeros(3))
D=3*s.eye(3)
assert E.T*G*E==s.zeros(3) and F.T*G*F==s.zeros(3)
assert E.T*G*F==s.eye(3) and R.T*G*E==s.zeros(3) and R.T*G*F==s.zeros(3)
assert R.T*G*R==D and s.Matrix.hstack(E,F,R).det()!=0
params=s.symbols('a:12');X=s.Matrix(s.symbols('x y z'))
K=s.Matrix([[0,params[0],params[1]],[-params[0],0,params[2]],[-params[1],-params[2],0]])
Z=s.Matrix(3,3,params[3:]);C=E+F*(K-Z.T*D*Z/2)+R*Z
assert s.simplify(C.T*G*C)==s.zeros(3)
print('frame verified',flush=True)
T=s.zeros(4)
for i,t in enumerate(C*X):T+=t*raw[i]
dump={'coordinates':['A11','A22','A33','A23','A13','A12','b1','b2','b3'],
      'tangent_basis':[[str(v) for v in m] for m in raw],
      'E':[[str(v) for v in E.row(i)] for i in range(9)],
      'F':[[str(v) for v in F.row(i)] for i in range(9)],
      'R':[[str(v) for v in R.row(i)] for i in range(9)],
      'D':[[str(v) for v in D.row(i)] for i in range(3)]}
(base/'witt-hadamard-frame.json').write_text(json.dumps(dump,indent=2))
# Ring multiplication avoids expression expansion overhead.
rr,*gens=ring(','.join([str(a) for a in params]+['x','y','z']),QQ)
TT=[[rr.from_expr(s.expand(T[i,j])) for j in range(4)] for i in range(4)]
eq=[]
for degree in [1,2,3,4]:
 pp=rr.zero
 for p in itertools.permutations(range(4)):
  for selected in itertools.combinations(range(4),degree):
   term=rr.one
   for i in selected:term*=TT[i][p[i]]
   pp+=term
 if degree<3:
  assert not pp
  print('degree',degree,'identically zero',flush=True)
  continue
 groups={}
 for mon,coeff in pp.items():
  exp=tuple(mon[-3:]);groups.setdefault(exp,[]).append((tuple(mon[:12]),coeff))
 for exp,terms in sorted(groups.items(),reverse=True):
  den=s.ilcm(*[int(c.denominator) for _,c in terms])
  ints=[(m,int(c*den)) for m,c in terms]
  gg=s.igcd(*[c for _,c in ints]);ints=[(m,c//gg) for m,c in ints]
  eq.append({'degree':degree,'monomial':exp,'terms':[[str(c),list(m)] for m,c in sorted(ints,reverse=True)]})
 print('degree',degree,'equations',len(groups),'total terms',len(pp),flush=True)
out={'parameters':[str(p) for p in params],'equations':eq,'chart':'E-coordinate block invertible; normalized to I3','frame':dump}
(base/'witt-hadamard-equations.json').write_text(json.dumps(out,indent=2))
print('DONE equations',len(eq),'terms',[len(q['terms']) for q in eq],flush=True)
