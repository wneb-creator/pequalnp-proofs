from pathlib import Path
from datetime import datetime, timezone
import hashlib,itertools,re
import sympy as s
root=Path(__file__).resolve().parent
source=root/'C4CoordinateInterface.lean'
text=source.read_text()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Source SHA256',hashlib.sha256(source.read_bytes()).hexdigest(),flush=True)
e,f,a,b,H,X,Y=s.symbols('e f a b H X Y')
loc={str(v):v for v in (e,f,a,b,H,X,Y)}
block=text.split('def scaledMatrix',1)[1].split('!![',1)[1].split(']',1)[0]
M=s.Matrix([[s.sympify(t.strip(),locals=loc) for t in row.split(',')] for row in block.split(';')])
assert M.shape==(4,4) and M==M.T
assert s.expand(sum(M))==0 and M[0,2]==M[1,3]==0
U=(a+b)/2;V=(b-a)/2
h=H/2;R=X/2+U/2;TT=Y/2-V/2
p=(e+f)/2;q=(e-f)/2;r=R-U;ss=TT+V
AA=h-e;u=(U+V)/2;v=(U-V)/2
BB=-2*(p+q)-AA
d0=(AA+u)/2;d2=(AA-u)/2;d1=(BB+v)/2;d3=(BB-v)/2
t01=(p+r)/2;t23=(p-r)/2;t12=(q+ss)/2;t03=(q-ss)/2
T=s.Matrix([[d0,t01,0,t03],[t01,d1,t12,0],[0,t12,d2,t23],[t03,0,t23,d3]])
assert all(s.expand(M[i,j]-8*T[i,j])==0 for i in range(4) for j in range(4))
print('All 16 Lean matrix entries equal 8 times reviewed coordinates; symmetry, tangent and support: PASS',flush=True)
q4=6*e**2+2*f**2+a**2+b**2-H**2-X**2-Y**2-X*(a+b)+Y*(b-a)
c16=2*f*a*b-2*H*X*Y+e*(-4*X**2-4*Y**2+4*X*(a+b)+4*Y*(a-b)-a**2-b**2+4*f**2)-4*e**3
for name,want,nextmark in [('quadratic',q4,'def cubic'),('cubic',c16,'lemma scaledMatrix_symmetric')]:
 expression=text.split('def '+name,1)[1].split(':=',1)[1].split(nextmark,1)[0].strip()
 assert s.expand(s.sympify(expression.replace('^','**'),locals=loc)-want)==0
print('Lean q/c definitions exactly match corrected Q4/C16: PASS',flush=True)
coefs=[]
for degree in range(5):
 out=0
 for mask in range(1,16):
  size=mask.bit_count()
  rows=[sum(M[i,j] for j in range(4) if mask>>j&1) for i in range(4)]
  out+=(-1)**(4-size)*size**(4-degree)*sum(s.prod(rows[i] for i in inds) for inds in itertools.combinations(range(4),degree))
 coefs.append(s.expand(out))
assert coefs[0]==24 and coefs[1]==0
assert s.expand(coefs[2]-16*q4)==0 and s.expand(coefs[3]-32*c16)==0
perm=sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))
assert s.expand(coefs[4]-perm)==0
assert s.expand(coefs[2]/8**2-q4/4)==0 and s.expand(coefs[3]/8**3-c16/16)==0
assert s.expand(c16.subs(e,0)-2*(f*a*b-H*X*Y))==0
print('Independent Ryser expansion: 24 + 16*q*z^2 + 32*c*z^3 + per(M)*z^4: PASS',flush=True)
print('Actual matrix M/8 has coefficients q/4, c/16; e=0 gives c=2*(f*a*b-H*X*Y): PASS',flush=True)
statement=text.split('lemma perm4',1)[1].split(':= by',1)[0].split('Matrix.permanent M =',1)[1]
terms=statement.split('+');perms=[]
for term in terms:
 pairs=[tuple(map(int,x)) for x in re.findall(r'M ([0-3]) ([0-3])',term)]
 assert len(pairs)==4 and sorted(i for i,j in pairs)==list(range(4)) and sorted(j for i,j in pairs)==list(range(4))
 perms.append(tuple(dict(pairs)[i] for i in range(4)))
assert len(perms)==24 and set(perms)==set(itertools.permutations(range(4)))
print('Displayed Lean perm4 right side contains each permutation exactly once: PASS',flush=True)
print('No Lean compile or source mutation performed',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
