from itertools import combinations
from pathlib import Path
import sympy as s
import json

p,q,x,y,z,h=s.symbols('p q x y z h')
r=-p-q
a,f=(p+x)/2,(p-x)/2
b,e=(q+y)/2,(q-y)/2
c,d=(r+z)/2,(r-z)/2
T=s.Matrix([[0,a,b,c],[a,0,d,e],[b,d,0,f],[c,e,f,0]])
M=s.ones(4)+h*T
# Ryser subset permanent, independently of original permutation expansion.
per=0
for mask in range(1,16):
    columns=[i for i in range(4) if (mask>>i)&1]
    per+=(-1)**(4-len(columns))*s.prod(sum(M[i,j] for j in columns) for i in range(4))
coeff=s.Poly(s.expand(per-24),h)
D=p*p+q*q+r*r-x*x-y*y-z*z
E=p*q*r-x*y*z
assert coeff.coeff_monomial(h)==0
print('quadratic',s.factor(coeff.coeff_monomial(h*h)))
print('cubic',s.factor(coeff.coeff_monomial(h**3)))
print('quartic',s.factor(coeff.coeff_monomial(h**4)))
assert s.expand(coeff.coeff_monomial(h*h)-D)==0
assert s.expand(coeff.coeff_monomial(h**3)-E)==0
assert s.expand(coeff.coeff_monomial(h**4)-D**2/16)==0
print('PASS: Q=D, C=E, F=D²/16')
print('square coefficient determinant',s.Matrix([[1,0,1],[0,0,2],[0,1,1]]).det())
Path(__file__).with_suffix('.json').write_text(json.dumps({
 'quadratic':str(s.factor(coeff.coeff_monomial(h*h))),
 'cubic':str(s.factor(coeff.coeff_monomial(h**3))),
 'quartic':str(s.factor(coeff.coeff_monomial(h**4)))},indent=2)+'\n')
