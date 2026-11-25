from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
import sympy as s
from sympy.polys.rings import ring

base=Path(__file__).resolve().parent
source=base/'zero-edge-pencil.json'
target=base/'zero-edge-saturated-minor-01.json'
data=json.loads(source.read_text());satdata=json.loads(target.read_text())
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
names=['v'+str(i) for i in range(12)]
assert data['variables']==names and satdata['variables']==names+['sat']
assert satdata['base_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
assert satdata['base_source']==str(source) and satdata['diagonal_rows']==[0,1]
assert len(data['equations'])==12 and len(satdata['equations'])==13
assert satdata['equations'][:12]==data['equations']
x,y=s.symbols('x y');vs=s.symbols('v0:12');sat=s.Symbol('sat')
T=s.Matrix(data['matrix']).applyfunc(s.sympify)
assert T==T.T and T[0,1]==x and T[0,2]==y and T[0,3]==0
assert s.expand(sum(T))==0
D=s.Matrix([[s.expand(T[i,i]).coeff(x),s.expand(T[i,i]).coeff(y)] for i in range(4)])
minor=D.extract([0,1],[0,1]).det()
assert minor==vs[0]*vs[3]-vs[1]*vs[2]
assert s.expand(s.sympify(satdata['diagonal_minor'])-minor)==0
assert s.expand(s.sympify(satdata['equations'][-1])-(sat*minor-1))==0
print('Exact12equationprefix,13variableorder,basehash,minor01,saturation sign: PASS',flush=True)
rr,*gens=ring(','.join(['x','y']+names),s.QQ)
M=s.ones(4)+T
MR=[[rr.from_expr(M[i,j]) for j in range(4)] for i in range(4)]
P=rr.zero
for mask in range(1,16):
 term=rr.one
 for i in range(4):term*=sum((MR[i][j] for j in range(4) if mask>>j&1),rr.zero)
 P+=(-1)**(4-mask.bit_count())*term
P-=24
coeff={}
for mon,c in P.items():
 key=mon[:2]
 coeff[key]=coeff.get(key,0)+s.Rational(c)*s.prod(v**n for v,n in zip(vs,mon[2:]))
ordered=[s.expand(coeff[key]) for key in sorted(coeff,reverse=True)]
assert len(ordered)==12
for actual,expected in zip(ordered,data['equations']):assert s.expand(actual-s.sympify(expected))==0
print('All12 base coefficients and order independently reproduced by Ryser: PASS',flush=True)
print('BASE_SHA256',hashlib.sha256(source.read_bytes()).hexdigest(),flush=True)
print('SATURATION01_SHA256',hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
print('Scope: one rank-two diagonal-minor open chart; no solver or mathematical verdict',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
