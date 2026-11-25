"""Lift the Witt graph back to18 variables while retaining simple quadrics."""
from pathlib import Path
exec(Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/witt_hadamard.py').read_text().split('params=s.symbols')[0])
params=s.symbols('a:18');X=s.Matrix(s.symbols('x y z'))
K=s.Matrix([[0,params[0],params[1]],[-params[0],0,params[2]],[-params[1],-params[2],0]])
Z=s.Matrix(3,3,params[3:12])
S=s.Matrix([[params[12],params[13],params[14]],[params[13],params[15],params[16]],[params[14],params[16],params[17]]])
C=E+F*(K+S)+R*Z
assert s.simplify(C.T*G*C-(2*S+3*Z.T*Z))==s.zeros(3)
print('lifted frame verified',flush=True)
T=s.zeros(4)
for i,t in enumerate(C*X):T+=t*raw[i]
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
 if degree==1:
  assert not pp
  print('degree1 identically zero',flush=True)
  continue
 groups={}
 for mon,coeff in pp.items():groups.setdefault(tuple(mon[-3:]),[]).append((tuple(mon[:18]),coeff))
 for exp,terms in sorted(groups.items(),reverse=True):
  den=s.ilcm(*[int(c.denominator) for _,c in terms])
  ints=[(m,int(c*den)) for m,c in terms]
  gg=s.igcd(*[c for _,c in ints]);ints=[(m,c//gg) for m,c in ints]
  eq.append({'degree':degree,'monomial':exp,'terms':[[str(c),list(m)] for m,c in sorted(ints,reverse=True)]})
 print('degree',degree,'equations',len(groups),'total terms',len(pp),flush=True)
result={'parameters':[str(p) for p in params],'equations':eq,
 'chart':'E-coordinate projection invertible, normalized to I3; C=E+F(K+S)+RZ',
 'parameter_order':'K upper entries3, Z row-major9, S symmetric upper-triangle6',
 'quadratic_identity':'C^T G C = 2 S + 3 Z^T Z'}
(base/'witt-lifted-equations.json').write_text(json.dumps(result,indent=2))
print('DONE',len(eq),'equations; term counts',[len(q['terms']) for q in eq],flush=True)
