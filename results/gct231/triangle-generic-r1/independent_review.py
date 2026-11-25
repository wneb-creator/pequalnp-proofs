from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
import sympy as s
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
target=root/'triangle-generic-eleven-equations.json';assert sha(target)=='8ded9d5e1145761185086336d90b749165633b5bad27a9c8de1677e32617eb48'
d=json.loads(target.read_text());oldpath=root.parent/'triangle_concept/triangle-twelve-equations.json';assert sha(oldpath)==d['source_sha256']=='03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
a=json.loads(oldpath.read_text())
D,E,F,G,H,A,B,C,SS,T,w=s.symbols('D E F G H A B C S T w');X,Y,Z=s.symbols('X Y Z');vs=(D,E,F,G,H,A,B,C,SS,T,w);loc={str(v):v for v in (*vs,X,Y,Z)}
assert d['unknowns']==[str(v) for v in vs] and d['kernel_in_original_coordinates']==['1','S','T']
I=-D-E-F-G-H-2*(1+SS+T);J=E+H+2*(SS-A+C);K=G+I+2*(T-B-C)
M=s.Matrix([[D*X+E*Y,X,SS*Y,A*(X-Y)],[X,F*X+G*Z,T*Z,B*(X-Z)],[SS*Y,T*Z,H*Y+I*Z,C*(Y-Z)],[A*(X-Y),B*(X-Z),C*(Y-Z),J*(X-Y)+K*(X-Z)]])
got=s.Matrix([[s.sympify(t,locals=loc) for t in row] for row in d['matrix']]);assert all(s.expand(got[i,j]-M[i,j])==0 for i in range(4) for j in range(4))
assert M==M.T and s.expand(sum(M))==0 and all(s.expand(v)==0 for v in M.subs({X:1,Y:1,Z:1})[3,:])
oldvs=s.symbols(a['unknowns']);x,y,z=s.symbols('x y z');oloc=dict(zip(a['unknowns'],oldvs));oloc.update(x=x,y=y,z=z)
sub={s.Symbol(k):s.sympify(v,locals=loc) for k,v in d['parameter_substitution'].items()}
expected={'d0':D,'d1':E/SS,'d3':F,'d5':G/T,'d7':H/SS,'d8':I/T,'o0':A,'o1':-A/SS,'o3':B,'o5':-B/T,'o7':C/SS,'o8':-C/T,'x':X,'y':SS*Y,'z':T*Z}
assert sub=={s.Symbol(k):v for k,v in expected.items()}
oldM=s.Matrix([[s.sympify(v,locals=oloc) for v in row] for row in a['matrix']])
assert all(s.cancel(oldM[i,j].subs(sub,simultaneous=True)-M[i,j])==0 for i in range(4) for j in range(4))
for row in a['equations']:
 if row['monomial'] is None:assert s.cancel(s.sympify(row['coefficient'],locals=oloc).subs(sub,simultaneous=True))==0
print('All16 matrix entries, weighted edge pivots1/S/T, tangent, center kernel(1,1,1), and old star/minor equations: PASS',flush=True)
allvars=(X,Y,Z,*vs);zero=s.Poly(0,*allvars,domain=s.QQ);one=s.Poly(1,*allvars,domain=s.QQ)
entries=[[s.Poly(1+M[i,j],*allvars,domain=s.QQ) for j in range(4)] for i in range(4)]
per=zero
for mask in range(1,16):
 term=one
 for i in range(4):term*=sum((entries[i][j] for j in range(4) if mask>>j&1),zero)
 per+=(-1)**(4-mask.bit_count())*term
per-=24;coeffs={}
for powers,c in per.terms():coeffs.setdefault(powers[:3],{})[powers[3:]]=c
assert all(2<=sum(mon)<=4 for mon in coeffs)
oldrows={tuple(row['monomial']):s.sympify(row['coefficient'],locals=oloc) for row in a['equations'] if row['monomial'] is not None}
counts={2:0,3:0,4:0};termcount=0;monset=set()
for row in d['equations']:
 value=s.sympify(row['coefficient'],locals=loc);poly=s.Poly(value,*vs,domain=s.QQ)
 assert row['terms']==len(poly.terms());termcount+=len(poly.terms())
 if row['monomial'] is None:
  assert s.expand(value-(w*SS*T-1))==0 and row['kind']=='nonzero_kernel_coordinates';continue
 mon=tuple(row['monomial']);assert mon not in monset;monset.add(mon);counts[sum(mon)]+=1
 content=s.Rational(row['content']);assert content!=0
 assert dict(poly.mul_ground(content).terms())==coeffs[mon]
 pulled=s.cancel(oldrows[mon].subs(sub,simultaneous=True)*SS**mon[1]*T**mon[2])
 assert s.expand(pulled-content*value)==0
assert counts=={2:6,3:10,4:3} and {m for m in monset if sum(m)==4}=={(2,2,0),(2,0,2),(0,2,2)}
assert len(d['equations'])==20 and termcount==1050
print('Independent Ryser verifies every retained row and primitive content;6Q+10C+3quartics+inverse,11variables/20equations/1050terms: PASS',flush=True)
# Check reverse coordinate assignment for a candidate with generic center kernel.
d0,d1,d3,d5,d7,d8,o0,o1,o3,o5,o7,o8=[oloc[v] for v in a['unknowns']]
reverse={D:d0,E:SS*d1,F:d3,G:T*d5,H:SS*d7,A:o0,B:o3,C:SS*o7}
outer=[o0+SS*o1,o3+T*o5,SS*o7+T*o8]
center=s.expand(oldM[3,3].subs({x:1,y:SS,z:T}))
identity=s.expand(T*d8-I.subs(reverse,simultaneous=True)+center+2*sum(outer))
assert identity==0
print('Reverse assignment: center star equations fix outer ratios; center diagonal zero and tangent force T*d8=I. S*T inverse precisely covers the nonzero-coordinate assumption: PASS',flush=True)
print('Scope: necessary system only on the triangle stratum admitting a center-star kernel vector with all three coordinates nonzero. Edge weights retained; zero-coordinate kernel branches and sufficiency of omitted quartics are not claimed. No solver run.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
