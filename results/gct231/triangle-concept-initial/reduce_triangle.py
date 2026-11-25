"""Exact necessary reductions of the triangle/all-stars-dependent stratum."""
from pathlib import Path
import json,hashlib,itertools
import sympy as S
base=Path(__file__).resolve().parents[1];out=Path(__file__).parent
source=base/'fresh/triangle-star-dependent-equations.json';data=json.loads(source.read_text())
loc={name:S.Symbol(name) for name in data['unknowns']};x,y,z=S.symbols('x y z');loc.update(x=x,y=y,z=z)
eq={tuple(row['monomial']):S.sympify(row['coefficient'],locals=loc) for row in data['equations'] if row['monomial'] is not None}
zero={loc[name]:0 for name in ['d2','d4','d6']}
for axis,name in [(0,'d6'),(1,'d4'),(2,'d2')]:
 keys=[]
 for degree in (2,3,4):
  key=[0,0,0];key[axis]=degree;keys.append(tuple(key))
 q,c,f=[eq[key] for key in keys];d=loc[name]
 assert S.expand(d**4+f-d*c+d*d*q/2)==0
 print('PASS isolated-diagonal certificate',name,keys,flush=True)
reduced={key:S.expand(value.subs(zero)) for key,value in eq.items()}
for axis in range(3):
 key=[0,0,0];key[axis]=4;assert reduced[tuple(key)]==0
for quartic,cubic,diagonal in [
 ((3,1,0),(3,0,0),'d7'),((3,0,1),(3,0,0),'d8'),
 ((1,3,0),(0,3,0),'d3'),((0,3,1),(0,3,0),'d5'),
 ((1,0,3),(0,0,3),'d0'),((0,1,3),(0,0,3),'d1')]:
 assert S.expand(reduced[quartic]-loc[diagonal]*reduced[cubic])==0
 print('PASS redundant quartic',quartic,diagonal,cubic,flush=True)

a,b,c,d,e,f=[loc[name] for name in ['o0','o1','o3','o5','o7','o8']]
M=S.Matrix([[a,b,0],[c,0,d],[0,e,f]])
t=S.Matrix([[loc['d0']+loc['d3']+2,loc['d1']+loc['d7']+2,loc['d5']+loc['d8']+2]])
assert S.expand(M.det()+a*d*e+b*c*f)==0
original_matrix=S.Matrix([[S.sympify(text,locals=loc).subs(zero) for text in row] for row in data['matrix']])
diag3=S.Matrix([[S.diff(original_matrix[3,3],u) for u in [x,y,z]]])
assert (diag3+t+2*(M[0,:]+M[1,:]+M[2,:])).applyfunc(S.expand)==S.zeros(1,3)
records=[]
for key,value in reduced.items():
 if sum(key)==4 and max(key)>2:continue
 records.append({'monomial':list(key),'coefficient':str(value),'kind':'original_after_forced_diagonal_zeros'})
assert len(records)==22
star=a*d*e+b*c*f
raw_star=[row for row in data['equations'] if row['monomial'] is None]
assert len(raw_star)==1 and S.expand(S.sympify(raw_star[0]['coefficient'],locals=loc)-star)==0
records.append({'monomial':None,'coefficient':str(star),'kind':'remaining_star_determinant'})
for i,j in itertools.combinations(range(3),2):
 relation=S.factor(S.Matrix.vstack(M[i,:],M[j,:],t).det())
 records.append({'monomial':None,'coefficient':str(relation),'kind':f'center_diagonal_minor_{i}_{j}'})
 print('CENTER_RELATION',i,j,relation,flush=True)
unknowns=[name for name in data['unknowns'] if name not in ['d2','d4','d6']]
result={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'unknowns':unknowns,'equations':records,'matrix':[[str(value) for value in row] for row in original_matrix.tolist()],
 'forced_zero_parameters':['d2','d4','d6'],
 'scope':'Necessary twelve-variable system for the triangle chart conditional on all four star determinants vanishing. Three diagonal zeros and three center-diagonal minors are derived from the isolated-vertex lemma; not a whole-gap result or an inconsistency verdict.'}
(out/'triangle-twelve-equations.json').write_text(json.dumps(result,indent=2)+'\n')
print('EXPORT',len(unknowns),len(records),'terms',sum(len(S.Poly(S.sympify(row['coefficient'],locals=loc),*[loc[n] for n in unknowns]).terms()) for row in records),flush=True)

# Universal quartic double-point coefficient calculation at (1,1,1).
A,B,C,D,E,G=S.symbols('A B C D E G')
quartic=A*x*x*y*y+B*x*x*z*z+C*y*y*z*z+D*x*x*y*z+E*x*y*y*z+G*x*y*z*z
grad=[S.diff(quartic,u).subs({x:1,y:1,z:1}) for u in [x,y,z]]
replacement={D:C-A-B,E:B-A-C,G:A-B-C}
assert all(S.expand(value.subs(replacement))==0 for value in grad)
assert S.Matrix([[S.diff(value,u) for u in [D,E,G]] for value in grad]).det()==4
q1=x*(y-z);q2=y*(x-z)
assert S.expand(quartic.subs(replacement)-(B*q1*q1+C*q2*q2+(A-B-C)*q1*q2))==0
print('PASS fourth double-point quartic normal form; mixed coefficient matrix determinant4',flush=True)

# Counterexample to inferring common kernel/symmetry from row-rank+tangent alone.
sample={a:2,b:3,c:-3,d:-9,e:-4,f:8,**{loc[n]:0 for n in unknowns if n.startswith('d')}}
assert star.subs(sample)==0
smat=original_matrix.subs(sample)
assert S.expand(sum(smat))==0
for i in range(4):
 rows=S.Matrix([[S.diff(smat[i,j],u) for u in [x,y,z]] for j in range(4)])
 assert rows.rank()==2
at_one=smat.subs({x:1,y:1,z:1});det=at_one.det();assert det!=0
qsample=S.factor(sum(reduced[key].subs(sample)*S.prod(u**n for u,n in zip([x,y,z],key)) for key in reduced if sum(key)==2))
assert qsample!=0
vectors=[S.Matrix([S.diff(smat[i,j],u) for i in range(4) for j in range(4)]) for u in [x,y,z]]
span=S.Matrix.hstack(*vectors);symmetries=[]
for perm in itertools.permutations(range(4)):
 permuted=S.Matrix.hstack(*[S.Matrix([S.diff(smat[perm[i],perm[j]],u) for i in range(4) for j in range(4)]) for u in [x,y,z]])
 if S.Matrix.hstack(span,permuted).rank()==3:symmetries.append(perm)
print('EXACT_WEAK_PREMISE_COUNTEREXAMPLE',{'parameters':{str(k):str(v) for k,v in sample.items()},'det_at_111':str(det),'quadratic_coefficient':str(qsample),'permutation_stabilizer':symmetries},flush=True)
print('SCOPE sample violates quadratic condition; it only blocks deductions from tangent/row-rank conditions alone.',flush=True)
