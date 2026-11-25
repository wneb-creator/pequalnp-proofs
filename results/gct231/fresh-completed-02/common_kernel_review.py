"""Independent exact common-kernel checks, using Ryser for the radical plane."""
from datetime import datetime,timezone
import hashlib
import itertools
from pathlib import Path
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import QQ


base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('Source SHA256',hashlib.sha256((base/'common_kernel_radical.py').read_bytes()).hexdigest(),flush=True)

B,C,D,E,F,ss=s.symbols('B C D E F ss')
M=s.Matrix([[0,B,C],[B,D,E],[C,E,F]])
q=s.expand(s.trace(M*M)-2*ss*(M[:,0].T*M[:,0])[0])
assert s.expand(q-(2*(1-ss)*(B*B+C*C)+D*D+F*F+2*E*E))==0
gram=s.hessian(q,[B,C,D,E,F])/2
print('Nonisotropic w normal form determinant',s.factor(gram.det()),flush=True)
assert gram.subs(ss,1).rank()==3
assert gram.subs(ss,1).nullspace()==[s.Matrix([1,0,0,0,0]),s.Matrix([0,1,0,0,0])]

A,B,C,E,F=s.symbols('A B C E F')
ww=s.Matrix([1,s.I,0])
M=s.Matrix([[A,B,C],[B,A+2*s.I*B,E],[C,E,F]])
assert s.expand((ww.T*M*ww)[0])==0
q=s.expand(s.trace(M*M)-2*((M*ww).T*(M*ww))[0])
assert s.expand(q-(2*(A+s.I*B)**2+F*F+4*E*E-4*s.I*C*E))==0
gram=s.hessian(q,[A,B,C,E,F])/2
assert gram.rank()==4
assert gram.nullspace()==[s.Matrix([-s.I,1,0,0,0])]
assert M.subs({A:-s.I,B:1,C:0,E:0,F:0})==-s.I*ww*ww.T
print('Isotropic nonzero w normal form rank4; radical exactly span(ww^T)',flush=True)

a,b,c,h,x,y,z=s.symbols('a b c h x y z')
w=s.Matrix([a,b,c,1-a-b-c])
delta=w[0]-w[3]
u=s.Matrix([(w[3]-w[1])*x+(w[3]-w[2])*y,delta*x,delta*y,
            -(w[0]-w[1])*x-(w[0]-w[2])*y])
assert s.expand(sum(u))==0 and s.expand((w.T*u)[0])==0
ubasis=s.Matrix.hstack(u.diff(x),u.diff(y))
assert s.expand(ubasis.extract([1,2],[0,1]).det()-delta**2)==0
T=w*u.T+u*w.T
rr,*gens=ring('a,b,c,x,y,z',QQ)
MM=[[rr.from_expr(s.expand(1+z*T[i,j])) for j in range(4)] for i in range(4)]
per=rr.zero
for size in range(1,5):
    for subset in itertools.combinations(range(4),size):
        term=rr.one
        for i in range(4):term*=sum((MM[i][j] for j in subset),rr.zero)
        per+=(-1)**(4-size)*term
per-=24
groups={}
for mon,coefficient in per.items():
    key=(mon[5],mon[3],mon[4])
    groups.setdefault(key,0)
    groups[key]+=s.Rational(coefficient.numerator,coefficient.denominator)*a**mon[0]*b**mon[1]*c**mon[2]
assert all(k[0]>=2 for k,v in groups.items() if v!=0)
norm=s.expand((w.T*w)[0]-1)
normideal=s.groebner([norm],a,b,c)
assert all(normideal.reduce(v)[1]==0 for key,v in groups.items() if key[0]==2)
equations=[norm,h*delta-1]+[v for key,v in groups.items() if key[0] in (3,4)]
print('Independent Ryser coefficient counts', {k:sum(1 for key in groups if key[0]==k) for k in (2,3,4)},flush=True)
gb=s.groebner(equations,h,a,b,c,domain=s.QQ,order='grevlex')
expected=s.groebner([a*a-a,h-2*a+1,b,c],h,a,b,c,domain=s.QQ,order='grevlex')
assert list(gb)==list(expected)
print('Independent Ryser radical-plane Groebner basis',list(gb),flush=True)
for aval,hval,which in [(0,-1,3),(1,1,0)]:
    point={a:aval,b:0,c:0,h:hval}
    assert all(s.expand(e.subs(point))==0 for e in equations)
    assert w.subs(point)==s.eye(4)[:,which]
print('The chart solutions are exactly w=e0 and w=e3; permutation coverage reviewed separately',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
