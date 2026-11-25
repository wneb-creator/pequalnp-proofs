"""Tiny exact diagnostic: symmetric3x3 constant-permanent pencils with a missing edge."""
from pathlib import Path
import json,time,signal,resource
import sympy as S
out=Path(__file__).parent
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
def limited(*_):raise TimeoutError('ten-second exact diagnostic cap')
signal.signal(signal.SIGALRM,limited)
x,y,p,q,r,s=S.symbols('x y p q r s')
matrix=S.Matrix([[p*x+q*y,0,x],[0,r*x+s*y,y],[x,y,-(p+r+2)*x-(q+s+2)*y]])
affine=S.ones(3)+matrix
per=0
for mask in range(1,8):
 cols=[j for j in range(3) if mask>>j&1]
 per+=(-1)**(3-len(cols))*S.prod(sum(affine[i,j] for j in cols) for i in range(3))
poly=S.Poly(S.expand(per-6),x,y);eq=[c for m,c in poly.terms()]
data={'unknowns':list(map(str,[p,q,r,s])),'matrix':[[str(v) for v in row] for row in matrix.tolist()],'equations':[{'monomial':list(m),'coefficient':str(c)} for m,c in poly.terms()],
      'scope':'ExactQQ diagnostic for3x3 symmetric pencils with one identically zero off-diagonal entry and the other two independent. Not a general3x3 or L-gct-231 result.'}
(out/'three-by-three-path-equations.json').write_text(json.dumps(data,indent=2)+'\n')
start=time.monotonic();signal.alarm(10)
try:
 G=S.groebner(eq,p,q,r,s,domain=S.QQ,order='grevlex',method='buchberger')
 result={'status':'COMPLETED','basis':list(map(str,[g.as_expr() for g in G.polys])),'unit':len(G.polys)==1 and G.polys[0].as_expr()==1}
except (TimeoutError,MemoryError) as ex:result={'status':'UNKNOWN_RESOURCE_LIMIT','error':str(ex)}
finally:signal.alarm(0)
result.update(seconds=time.monotonic()-start,scope=data['scope'])
(out/'three-by-three-path-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
