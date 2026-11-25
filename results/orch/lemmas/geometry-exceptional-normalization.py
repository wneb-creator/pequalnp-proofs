from pathlib import Path
import sympy as s,itertools,json,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
a,r,z=s.symbols('a r z');T=s.Matrix([[0,1,r,0],[1,a,-a*r,0],[r,-a*r,a*r*r,0],[0,0,0,0]]);M=s.ones(4)+z*T;P=s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))));hs=a*(1-r)**2+2*(1+r);Q=r**4-4*r**3+14*r*r-4*r+1;q=s.expand(P.coeff(z,2));assert s.expand(P-24-6*hs*z-q*z*z)==0
res=s.factor(q.subs(a,-2*(1+r)/(1-r)**2));print('q',q,'substituted',res,flush=True)
mult=s.cancel(res*(1-r)**4/Q/(1+r)**2);assert mult.is_Rational;dividend=s.expand((1-r)**4*q-mult*(1+r)**2*Q);quo,rem=s.div(dividend,hs,a,r);assert rem==0
W=s.invert((1-r)**2,Q,r);target=4*a+3*r**3-11*r*r+37*r+3;H,rem=s.div(s.expand(target-4*W*hs),Q,a,r);assert rem==0
out={'quadratic':str(q),'sum':str(hs),'quartic':str(Q),'quartic_factor':str(mult),'quartic_sum_multiplier':str(quo),'alpha_sum_multiplier':str(4*W),'alpha_quartic_multiplier':str(H),'permanent':str(P)}
job=Path('/tmp/oec/pequalnp-pilot-79');(job/'geometry-exceptional-normalization-identities.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
