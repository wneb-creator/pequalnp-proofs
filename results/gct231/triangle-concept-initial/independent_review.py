from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,itertools
import sympy as s
out=Path(__file__).resolve().parent;root=out.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=root/'fresh/triangle-star-dependent-equations.json';target=out/'triangle-twelve-equations.json'
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Source SHA256',sha(source),'export SHA256',sha(target),flush=True)
a=json.loads(source.read_text());d=json.loads(target.read_text());assert d['source_sha256']==sha(source)
rawvars=s.symbols(a['unknowns']);loc=dict(zip(a['unknowns'],rawvars));x,y,z=s.symbols('x y z');loc.update(x=x,y=y,z=z)
M=s.Matrix([[s.sympify(v,locals=loc) for v in row] for row in a['matrix']])
assert M==M.T and s.expand(sum(M))==0
assert [M[0,1],M[0,2],M[1,2]]==[x,y,z]
allvars=(x,y,z,*rawvars);zero=s.Poly(0,*allvars,domain=s.QQ);one=s.Poly(1,*allvars,domain=s.QQ)
entries=[[s.Poly(1+M[i,j],*allvars,domain=s.QQ) for j in range(4)] for i in range(4)]
per=zero
for mask in range(1,16):
 term=one
 for i in range(4):term*=sum((entries[i][j] for j in range(4) if mask>>j&1),zero)
 per+=(-1)**(4-mask.bit_count())*term
per-=24
coefs={}
for powers,coeff in per.terms():coefs.setdefault(powers[:3],{})[powers[3:]]=coeff
eq={tuple(row['monomial']):s.sympify(row['coefficient'],locals=loc) for row in a['equations'] if row['monomial'] is not None}
assert len(coefs)==len(eq)==31
for mon,value in eq.items():assert coefs.pop(mon)==dict(s.Poly(value,*rawvars,domain=s.QQ).terms())
assert not coefs
print('Independent Ryser reconstruction of all 31 raw triangle coefficients: PASS',flush=True)
zeros={loc[name]:0 for name in ['d2','d4','d6']}
for axis,name in [(0,'d6'),(1,'d4'),(2,'d2')]:
 vertex={0:2,1:1,2:0}[axis]
 subs={v:int(i==axis) for i,v in enumerate((x,y,z))}
 assert all(M[vertex,j].subs(subs)==0 for j in range(4) if j!=vertex)
 assert M[vertex,vertex].subs(subs)==loc[name]
 ks=[]
 for degree in (2,3,4):
  k=[0,0,0];k[axis]=degree;ks.append(tuple(k))
 q,c,f=[eq[k] for k in ks];dd=loc[name]
 assert s.expand(dd**4+f-dd*c+dd**2*q/2)==0
print('Three axis isolated vertices and exact diagonal-power certificates: PASS',flush=True)
reduced={mon:s.expand(poly.subs(zeros)) for mon,poly in eq.items()}
for axis in range(3):
 mon=[0,0,0];mon[axis]=4;assert reduced[tuple(mon)]==0
for quartic,cubic,diagonal in [((3,1,0),(3,0,0),'d7'),((3,0,1),(3,0,0),'d8'),((1,3,0),(0,3,0),'d3'),((0,3,1),(0,3,0),'d5'),((1,0,3),(0,0,3),'d0'),((0,1,3),(0,0,3),'d1')]:
 assert s.expand(reduced[quartic]-loc[diagonal]*reduced[cubic])==0
expected={mon:poly for mon,poly in reduced.items() if not(sum(mon)==4 and max(mon)>2)}
assert len(expected)==22
newM=M.subs(zeros);gotM=s.Matrix([[s.sympify(v,locals=loc) for v in row] for row in d['matrix']]);assert newM==gotM
star=s.Matrix([[s.diff(newM[3,j],v) for v in (x,y,z)] for j in (0,1,2)])
diag=s.Matrix([[s.diff(newM[3,3],v) for v in (x,y,z)]])
t=s.Matrix([[loc['d0']+loc['d3']+2,loc['d1']+loc['d7']+2,loc['d5']+loc['d8']+2]])
assert (diag+t+2*(star[0,:]+star[1,:]+star[2,:])).applyfunc(s.expand)==s.zeros(1,3)
extra=[row for row in a['equations'] if row['monomial'] is None];assert len(extra)==1
starpoly=s.sympify(extra[0]['coefficient'],locals=loc)
assert s.expand(starpoly+star.det())==0
expected_extra={'remaining_star_determinant':starpoly}
for i,j in itertools.combinations(range(3),2):
 expected_extra[f'center_diagonal_minor_{i}_{j}']=s.Matrix.vstack(star[i,:],star[j,:],t).det()
 # The t-minor differs from the negative diagonal-minor only by a multiple
 # of the original star determinant, which vanishes in this stratum.
 identity=s.expand(s.Matrix.vstack(star[i,:],star[j,:],t).det()+s.Matrix.vstack(star[i,:],star[j,:],diag).det())
 remainder=s.Poly(identity,*rawvars,domain=s.QQ).rem(s.Poly(starpoly,*rawvars,domain=s.QQ)).as_expr()
 assert remainder==0
for row in d['equations']:
 got=s.sympify(row['coefficient'],locals=loc)
 if row['monomial'] is not None:
  assert row['kind']=='original_after_forced_diagonal_zeros'
  want=expected.pop(tuple(row['monomial']))
 else:want=expected_extra.pop(row['kind'])
 assert s.expand(got-want)==0
assert not expected and not expected_extra
assert d['unknowns']==[name for name in a['unknowns'] if name not in ['d2','d4','d6']]
assert d['forced_zero_parameters']==['d2','d4','d6'] and len(d['unknowns'])==12 and len(d['equations'])==26
nv=[loc[name] for name in d['unknowns']]
assert sum(len(s.Poly(s.sympify(row['coefficient'],locals=loc),*nv,domain=s.QQ).terms()) for row in d['equations'])==686
print('All 26 exported equations, 12 variables, 686 terms, six redundant quartics and three center-diagonal minors: PASS',flush=True)
A,B,C,D,E,G=s.symbols('A B C D E G');quartic=A*x*x*y*y+B*x*x*z*z+C*y*y*z*z+D*x*x*y*z+E*x*y*y*z+G*x*y*z*z
replacement={D:C-A-B,E:B-A-C,G:A-B-C}
grad=[s.diff(quartic,v).subs({x:1,y:1,z:1}) for v in (x,y,z)]
assert all(s.expand(v.subs(replacement))==0 for v in grad)
assert s.Matrix([[s.diff(v,u) for u in (D,E,G)] for v in grad]).det()==4
q1=x*(y-z);q2=y*(x-z)
assert s.expand(quartic.subs(replacement)-(B*q1*q1+C*q2*q2+(A-B-C)*q1*q2))==0
print('Optional quartic double-point normal form at (1,1,1): exact identity PASS',flush=True)
print('Mathematical scope: original all-four-stars-dependent stratum only. Isolated-vertex theorem forces the three diagonal zeros. At center3 its diagonal functional annihilates the kernel of the star map, hence belongs to its row span; star rank<=2 then gives all appended minors. No extra rank=2 or nonzero-coordinate hypothesis is needed for those necessary minors. No inconsistency verdict.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
