"""Rational form of the tiny coordinate-edge pencil obstruction."""
from pathlib import Path
import json,itertools,time,signal,resource
import sympy as S
out=Path(__file__).parent
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
def stop(*_):raise TimeoutError('ten-second exact diagnostic cap')
signal.signal(signal.SIGALRM,stop)
x,y,p,r,s,k=S.symbols('x y p r s k')
M=S.Matrix([[p*x,x,k*x],[x,r*x+s*y,y],[k*x,y,-(p+r+2+2*k)*x-(s+2)*y]])
N=S.ones(3)+M
poly=S.Poly(S.expand(sum(S.prod(N[i,pi[i]] for i in range(3)) for pi in itertools.permutations(range(3)))-6),x,y)
q=s*s+2*s-1
rvalue=-p/S.Integer(2)-2+(s+1)*(2*k+p+2)/4
equations=[q];records=[{'monomial':None,'coefficient':str(q),'kind':'single_edge_quadratic'}]
discarded=[]
for mon,coefficient in poly.terms():
 value=S.expand(coefficient.subs(r,rvalue))
 remainder=S.rem(value,q,s)
 assert S.rem(value-remainder,q,s)==0
 if remainder==0:discarded.append(list(mon));continue
 primitive=S.Poly(remainder,p,k,s,domain=S.QQ).clear_denoms()[1].primitive()[1].as_expr()
 if primitive in equations or -primitive in equations:continue
 equations.append(primitive);records.append({'monomial':list(mon),'coefficient':str(primitive),'kind':'necessary_remainder_mod_single_edge_quadratic'})
assert S.rem(S.expand(poly.coeff_monomial(x*y).subs(r,rvalue)),q,s)==0
# The x*y coefficient's r-coefficient is a nonzero multiple of s+1;
# (s+1)^2=2 on q=0, so solving for r is legitimate over C.
rcoefficient=S.diff(poly.coeff_monomial(x*y),r)
assert S.Poly(rcoefficient,s).degree()==1
assert S.rem(S.expand(rcoefficient),q,s)!=0
print('LINEAR_R_COEFFICIENT',S.factor(rcoefficient),'R_VALUE',rvalue,flush=True)
data={'unknowns':['p','k','s'],'equations':records,'r_substitution':str(rvalue),
 'r_coefficient':str(rcoefficient),'discarded_zero_remainders':discarded,
 'scope':'Necessary exactQQ system for3x3 symmetric coordinate-edge pencils. Requires the separately proved3x3 isolated diagonal zero and chart normalization; no whole-gap or Lean claim.'}
(out/'three-by-three-axis-qq-equations.json').write_text(json.dumps(data,indent=2)+'\n')
start=time.monotonic();signal.alarm(10)
try:
 G=S.groebner(equations,p,k,s,domain=S.QQ,order='grevlex')
 result={'status':'COMPLETED','basis':list(map(str,[v.as_expr() for v in G.polys])),'unit':len(G.polys)==1 and G.polys[0].as_expr()==1}
except (TimeoutError,MemoryError) as exc:result={'status':'UNKNOWN_RESOURCE_LIMIT','error':str(exc)}
finally:signal.alarm(0)
result.update(seconds=time.monotonic()-start,equation_count=len(equations),term_count=sum(len(S.Poly(e,p,k,s).terms()) for e in equations),scope=data['scope'])
(out/'three-by-three-axis-qq-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
