from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,itertools
import sympy as s

base=Path(__file__).resolve().parent
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for name in ['c4_factor_coordinates.py','c4_factor_coordinates.json','c4_opposite_recentered.json']:
 print('SHA256',name,hashlib.sha256((base/name).read_bytes()).hexdigest(),flush=True)
e,f,a,b,H,X,Y,z=s.symbols('e f a b H X Y z')
coords=(e,f,a,b,H,X,Y)
# Invert the stated recentering and factor-coordinate maps, then construct T.
U=(a+b)/2;V=(b-a)/2
h=H/2;R=X/2+U/2;TT=Y/2-V/2
p=(e+f)/2;q=(e-f)/2;r=R-U;ss=TT+V
AA=h-e;u=(U+V)/2;v=(U-V)/2
BB=-2*(p+q)-AA
d0=(AA+u)/2;d2=(AA-u)/2;d1=(BB+v)/2;d3=(BB-v)/2
t01=(p+r)/2;t23=(p-r)/2;t12=(q+ss)/2;t03=(q-ss)/2
T=s.Matrix([[d0,t01,0,t03],[t01,d1,t12,0],[0,t12,d2,t23],[t03,0,t23,d3]])
assert s.expand(sum(T))==0
entries=[T[0,0],T[1,1],T[2,2],T[0,1],T[0,3],T[1,2],T[2,3]]
jac=s.Matrix(entries).jacobian(coords)
assert jac.det()!=0
print('Coordinate map invertible, determinant',jac.det(),flush=True)
components=[]
for degree in (2,3):
 ans=0
 for mask in range(1,16):
  size=mask.bit_count()
  rows=[sum(T[i,j] for j in range(4) if mask>>j&1) for i in range(4)]
  ans+=(-1)**(4-size)*size**(4-degree)*sum(s.prod(rows[i] for i in inds) for inds in itertools.combinations(range(4),degree))
 components.append(s.expand(ans))
q4=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c16=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a**2-b**2+4*f**2)-4*e**3
assert s.expand(4*components[0]-q4)==0
assert s.expand(16*components[1]-c16)==0
saved=json.loads((base/'c4_factor_coordinates.json').read_text())
assert s.expand(s.sympify(saved['Q4'])-q4)==0
assert s.expand(s.sympify(saved['C16'])-c16)==0
print('Corrected scaled Q4 and C16 independently verified by Ryser',flush=True)
assert s.expand(c16.subs(e,0)/2-(f*a*b-H*X*Y))==0
vs=(f,a,b,H,X,Y)
records=[]
for first in (f,a,b):
 for second in (H,X,Y):
  keep=[v for v in vs if v not in (first,second)]
  G=s.hessian(q4.subs({e:0,first:0,second:0}),keep)/2
  assert G.det()!=0 and G.rank()==4
  print('ZERO_FACTOR',first,second,'rank4 determinant',G.det(),flush=True)
  records.append({'zero':[str(first),str(second)],'coordinates':list(map(str,keep)),
                  'gram':[[str(v) for v in G.row(i)] for i in range(4)],'determinant':str(G.det())})
(base/'c4-factor-zero-branch-review.json').write_text(json.dumps(records,indent=2)+'\n')
print('Every zero-product branch has Witt index2; no isotropic3-plane',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
