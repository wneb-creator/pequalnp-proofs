"""Independent determinant replay and elementary certificates; no Groebner calls."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,itertools
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
coords=(e,f,a,b,H,X,Y)
u,v,lam=s.symbols('u v lam')
data=json.loads((base/'c4_factor_coordinates.json').read_text())
q=s.sympify(data['Q4']);c=s.sympify(data['C16'])
records=json.loads((base/'fresh/c4-zero-product-square-test.json').read_text())
assert len(records)==9
print('Parent source SHA256',hashlib.sha256((base/'fresh/c4_zero_product_pencil.py').read_bytes()).hexdigest(),flush=True)
print('Parent records SHA256',hashlib.sha256((base/'fresh/c4-zero-product-square-test.json').read_bytes()).hexdigest(),flush=True)
G=s.hessian(q,coords)/2
gradient=s.Matrix([s.diff(c,z) for z in coords])
verified={}
for record in records:
 left,right=map(s.Symbol,record['zero_coordinates'])
 W=[z for z in coords if z not in (e,left,right)]
 inds=[coords.index(z) for z in W]
 GW=G.extract(inds,inds)
 assert GW.det()!=0
 w=s.Matrix([s.sympify(record['w'][str(z)]) for z in coords])
 assert w[0]==1 and w[coords.index(left)]==u and w[coords.index(right)]==v
 assert all((G*w)[j]==0 for j in inds)
 qw=s.expand(q.subs(dict(zip(coords,w)),simultaneous=True))
 cw=s.expand(c.subs(dict(zip(coords,w)),simultaneous=True))
 assert s.expand(qw-s.sympify(record['q_w']))==0
 assert s.expand(cw-s.sympify(record['c_w']))==0
 ksub={e:0,left:0,right:0}
 R=s.expand((gradient.subs(ksub).T*w)[0])
 B=s.hessian(R,W)/2
 # Characteristic polynomial supplies a different determinant computation.
 determinant=(GW.inv()*B).charpoly(lam).as_expr()
 assert s.expand(determinant-s.sympify(record['det_monic']))==0
 c3,c2,c1,c0=s.Poly(determinant,lam).all_coeffs()[1:]
 sq3=s.expand(8*c1-4*c3*c2+c3**3)
 sq4=s.expand(64*c0-(4*c2-c3*c3)**2)
 assert s.expand(sq3-s.sympify(record['square_cubic']))==0
 assert s.expand(sq4-s.sympify(record['square_quartic']))==0
 verified[(str(left),str(right))]=(qw,cw,sq3)
 print('NORMALIZATION_AND_DETERMINANT',left,right,'PASS',flush=True)

# Monic quartic square conditions follow from coefficient comparison.
aa,bb=s.symbols('A B')
sq=s.Poly((lam**2+aa*lam+bb)**2,lam)
d3,d2,d1,d0=sq.all_coeffs()[1:]
assert s.expand(8*d1-4*d3*d2+d3**3)==0
assert s.expand(64*d0-(4*d2-d3*d3)**2)==0

certificate_data=[]
for pair,(qw,cw,sc) in verified.items():
 if pair==('f','H'):
  Q=qw;C=cw/4;S=sc*s.Rational(27,64)
  assert s.expand(S-2*Q-9*C)==-3
  certificate_data.append({'case':pair,'identity':'S-2Q-9C=-3',
                           'normalizations':['Q=q_w','C=c_w/4','S=27*square_cubic/64']})
 elif pair in [('f','X'),('f','Y')]:
  sub={u:-u} if pair[1]=='Y' else {}
  Q=s.expand(2*qw.subs(sub));C=s.expand(2*cw.subs(sub));S=s.expand(-27*sc.subs(sub))
  assert s.expand(Q-(4*u*u-3*v*v+12))==0
  assert s.expand(C-(u-1)*(8*u+v*v+8))==0
  F=(u-1)*(u+3)**2
  R=57*u**3-391*u**2+723*u+571
  assert s.expand(3*C+(u-1)*Q-4*F)==0
  assert s.expand(S+(8*u+56)*Q-R)==0
  assert R.subs(u,1)==960 and R.subs(u,-3)==-6656
  certificate_data.append({'case':pair,'F':str(F),'R':str(R),'values':[960,-6656]})
 elif pair in [('a','H'),('b','H')]:
  sub={v:-v} if pair[0]=='b' else {}
  Q=s.expand(2*qw.subs(sub));C=s.expand(-2*cw.subs(sub));S=s.expand(-27*sc.subs(sub))
  assert s.expand(Q-(3*u*u-2*v*v+12))==0
  assert s.expand(C-(u*u*(v+14)+8))==0
  F=v**3+14*v**2-6*v-72
  R=33*v**3+104*v**2+1632*v+4096
  assert s.expand(3*C-(v+14)*Q-2*F)==0
  assert s.expand(S-(4*v-128)*Q-R)==0
  A=116068029*v**2+76597820*v+5448726416
  B=-3517213*v**2-40477578*v+125002182
  assert s.expand(A*F+B*R)==119700635520
  certificate_data.append({'case':pair,'F':str(F),'R':str(R),
                           'bezout_F':str(A),'bezout_R':str(B),'constant':119700635520})
 else:
  assert pair in [('a','X'),('a','Y'),('b','X'),('b','Y')]
  sub={v:-v} if pair==('b','Y') else {}
  Q=s.expand(s.Rational(5,6)*qw.subs(sub))
  C=s.expand(-s.Rational(25,2)*cw.subs(sub))
  S=s.expand(s.Rational(125,8)*sc.subs(sub))
  assert s.expand(Q-(u*u-u*v-v*v+5))==0
  assert s.expand(C-(37*u*u-82*u*v+38*v*v+50))==0
  assert s.expand(S-(130*u*u-40*v*v-63))==0
  M=s.Matrix([[1,-1,-1],[37,-82,38],[130,0,-40]])
  values=s.Matrix([1464,2755,3309])/920
  assert M.det()!=0
  assert M*values==s.Matrix([-5,-50,63])
  assert values[1]**2-values[0]*values[2]==s.Rational(1657**2,920**2)
  certificate_data.append({'case':pair,'monomials':['u^2','uv','v^2'],
                           'values':list(map(str,values)),'contradiction':'1657^2/920^2'})
 print('ELEMENTARY_CONTRADICTION',pair,'PASS',flush=True)

(base/'c4-zero-product-independent-certificates.json').write_text(json.dumps(certificate_data,indent=2)+'\n')
print('All9 cases excluded by q(w), c(w), and square_cubic alone; no Groebner computation',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
