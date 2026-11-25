"""Necessary-line resultant and Bezout obstruction for isotropic kernels."""
from pathlib import Path
import json
exec(Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh/rowzero_nilpotent.py').read_text().split('G=s.groebner')[0])
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
A=s.expand(sum(s.prod(k[i] for i in inds) for inds in itertools.combinations(range(4),3)))
B=s.expand(s.prod(k))
assert s.expand(A+16*s.I*t*(t**4-1))==0
assert s.expand(B-4*(t**8+14*t**4+1))==0
r,q,AA,BB,xx,yy,mu=s.symbols('r q A B X Y mu')
es=[1,0,0,AA,BB]
universal=0
for j in [0,3,4]:
 pp=s.Poly((xx+r*yy)**(4-j)*(r*xx+q*yy)**j,xx,yy)
 for ell in [0,3,4]:
  universal+=es[j]*es[ell]*s.factorial(4-ell)*s.factorial(ell)*pp.coeff_monomial(xx**(4-ell)*yy**ell)
expected=24+48*AA*r**3+48*BB*r**4+6*AA**2*q**3+18*AA**2*r**2*q**2+48*AA*BB*r*q**3+24*BB**2*q**4
assert s.expand(universal-expected)==0
line=s.Poly(s.expand(universal.subs({r:xx,q:2*mu*xx})-24),xx)
assert s.expand(line.nth(3)-48*AA*(1+AA*mu**3))==0
assert s.expand(line.nth(4)-(48*BB+72*AA**2*mu**2+384*AA*BB*mu**3+384*BB**2*mu**4))==0
print('universal rank2 coefficient identity checked',flush=True)
RR=s.Poly(result,t,domain=s.QQ).primitive()[1]
YY=s.Poly(s.expand((A/s.I)*(A**4-8*B**3)*(27*A**4-512*B**3)),t,domain=s.QQ).primitive()[1]
u,v,g=s.gcdex(RR,YY)
assert g.as_expr()==1 and (u*RR+v*YY-g).is_zero
print('RESULTANT_DEGREE',RR.degree(),'SECOND_NECESSARY_DEGREE',YY.degree(),'GCD',g.as_expr(),flush=True)
print('BEZOUT_IDENTITY_VERIFIED',flush=True)
dump={'R':[str(c) for c in RR.all_coeffs()],'Y':[str(c) for c in YY.all_coeffs()],
 'bezout_R':[str(c) for c in u.all_coeffs()],'bezout_Y':[str(c) for c in v.all_coeffs()],
 'identity':'bezout_R*R+bezout_Y*Y=1; coefficients descending degree'}
(base/'isotropic-kernel-bezout.json').write_text(json.dumps(dump,indent=2))
# The remaining conic point is t=infinity in the reciprocal parameter.
ki=H*s.Matrix([0,-1,s.I,0]);vi=H*s.Matrix([0,0,0,2])+l*ki
Ti=ki*vi.T+vi*ki.T
hi=s.symbols('h');Mi=s.ones(4)+hi*Ti
pi=s.Poly(s.expand(sum(s.prod(Mi[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24),hi)
assert s.expand(pi.nth(3)+2048*l)==0
assert s.expand(pi.nth(4)-(6144*l**4+3072))==0
print('INFINITY_CHART cubic=-2048*l quartic=6144*l^4+3072',flush=True)
print('ALL_CERTIFICATE_CHECKS_PASSED',flush=True)
