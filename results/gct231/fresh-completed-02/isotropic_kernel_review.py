"""Independent Witt normal forms, Ryser line coefficients, and Bezout replay."""
from datetime import datetime,timezone
import hashlib
import itertools
import json
from pathlib import Path
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import QQ_I


base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for name in ('isotropic_kernel_certificate.py','rowzero_nilpotent.py','isotropic-kernel-bezout.json'):
    print('SHA256',name,hashlib.sha256((base/name).read_bytes()).hexdigest(),flush=True)
aa,bb,cc,dd,ee,ff,q=s.symbols('a b c d e f q')
J=s.Matrix([[0,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]])
S=s.Matrix([[aa,0,bb,cc],[0,0,0,0],[bb,0,dd,ee],[cc,0,ee,ff]])
T=S*J
assert T*s.eye(4)[:,0]==s.zeros(4,1)
v=s.Matrix([2/q,q,0,0])
assert s.simplify((v.T*J*v)[0])==4
assert s.simplify((v.T*J*T*v)[0])==q*q*aa
quad=s.expand(s.trace(T*T)-2*((T*v).T*J*(T*v))[0])
assert s.expand(quad.subs(aa,0)-(dd*dd+ff*ff+2*ee*ee-2*q*q*(bb*bb+cc*cc)))==0
assert s.factor((s.hessian(quad.subs(aa,0),[bb,cc,dd,ee,ff])/2).det())==8*q**4
v=s.Matrix([0,0,2,0])
assert (v.T*J*T*v)[0]==4*dd
quad=s.expand(s.trace(T*T)-2*((T*v).T*J*(T*v))[0])
assert s.expand(quad.subs(dd,0)-(ff*ff-6*ee*ee))==0
assert (s.hessian(quad.subs(dd,0),[aa,bb,cc,ee,ff])/2).rank()==2
print('Both isotropic-kernel tangent quadratics checked in an explicit Witt metric',flush=True)

t,l,h,mu=s.symbols('t l h mu')
H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
k=H*s.Matrix([0,1-t*t,s.I*(1+t*t),2*t])
kp=k.diff(t);ones=s.ones(4,1)
assert s.expand(sum(k))==s.expand((k.T*k)[0])==0
assert s.expand(sum(kp))==s.expand((k.T*kp)[0])==0
assert s.expand((kp.T*kp)[0])==16
assert s.expand((1-t*t)-s.I*(s.I*(1+t*t)))==2
print('Finite conic parameter and derivative checks passed; derivative norm16',flush=True)

def ryser_coefficients(T,parameters):
    rr,*gens=ring(','.join(map(str,parameters))+',h',QQ_I)
    entries=[[rr.from_expr(s.expand(1+h*T[i,j])) for j in range(4)] for i in range(4)]
    per=rr.zero
    for size in range(1,5):
        for subset in itertools.combinations(range(4),size):
            term=rr.one
            for i in range(4):term*=sum((entries[i][j] for j in subset),rr.zero)
            per+=(-1)**(4-size)*term
    expression=per.as_expr()-24
    return s.Poly(expression,h)

v=kp+l*k
first=ryser_coefficients(k*v.T+v*k.T,[t,l])
assert first.nth(1)==first.nth(2)==0
C,Q=map(s.expand,(first.nth(3),first.nth(4)))
RR=s.Poly(s.resultant(C,Q,l),t,domain=s.QQ).primitive()[1]
print('Independent first-line resultant degree',RR.degree(),flush=True)

A=s.expand(sum(s.prod(k[i] for i in indices) for indices in itertools.combinations(range(4),3)))
B=s.expand(s.prod(k))
assert s.expand(A+16*s.I*t*(t**4-1))==0
assert s.expand(B-4*(t**8+14*t**4+1))==0
u=ones+mu*k
second=ryser_coefficients(k*u.T+u*k.T,[t,mu])
assert second.nth(1)==second.nth(2)==0
assert s.expand(second.nth(3)-48*A*(1+A*mu**3))==0
assert s.expand(second.nth(4)-(48*B+72*A*A*mu*mu+384*A*B*mu**3+384*B*B*mu**4))==0
AA,BB=s.symbols('A B')
f=48*AA*(1+AA*mu**3)
g=48*BB+72*AA*AA*mu*mu+384*AA*BB*mu**3+384*BB*BB*mu**4
res=s.factor(s.resultant(f,g,mu))
assert res==73383542784*AA**4*(AA**4-8*BB**3)*(27*AA**4-512*BB**3)
YY=s.Poly(s.expand((A/s.I)*(A**4-8*B**3)*(27*A**4-512*B**3)),t,domain=s.QQ).primitive()[1]
print('Second-line coefficients independently checked; necessary polynomial degree',YY.degree(),flush=True)

artifact=json.loads((base/'isotropic-kernel-bezout.json').read_text())
read=lambda key:s.Poly.from_list([s.Rational(c) for c in artifact[key]],gens=t,domain=s.QQ)
assert read('R')==RR and read('Y')==YY
assert read('bezout_R')*RR+read('bezout_Y')*YY==s.Poly(1,t,domain=s.QQ)
print('Exported rational Bezout identity exactly replayed against independent R and Y',flush=True)

ki=H*s.Matrix([0,-1,s.I,0])
derivative=H*s.Matrix([0,0,0,2])
vi=derivative+l*ki
infinity=ryser_coefficients(ki*vi.T+vi*ki.T,[l])
assert s.expand(infinity.nth(3)+2048*l)==0
assert s.expand(infinity.nth(4)-(6144*l**4+3072))==0
print('Infinity line: cubic−2048lambda; quartic6144lambda^4+3072, hence incompatible',flush=True)
print('No full FGLM calculation used; only exact necessary-line identities and Bezout replay',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
