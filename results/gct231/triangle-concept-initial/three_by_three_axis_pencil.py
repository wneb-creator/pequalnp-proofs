"""Exact tiny elimination for a3x3 constant-permanent pencil containing an edge direction."""
from pathlib import Path
import json,itertools,time
import sympy as S
out=Path(__file__).parent
x,y,p,r,s,k=S.symbols('x y p r s k')
M=S.Matrix([[p*x,x,k*x],[x,r*x+s*y,y],[k*x,y,-(p+r+2+2*k)*x-(s+2)*y]])
N=S.ones(3)+M
per=S.expand(sum(S.prod(N[i,perm[i]] for i in range(3)) for perm in itertools.permutations(range(3)))-6)
pol=S.Poly(per,x,y);eq={mon:coef for mon,coef in pol.terms()}
assert eq[(0,2)]==-(s*s+2*s-1)
for sign in [-1,1]:
 root=-1+sign*S.sqrt(2)
 linear=S.expand(eq[(1,1)].subs(s,root));assert S.Poly(linear,p,r,k).total_degree()==1
 solved=S.solve(linear,r);assert len(solved)==1
 sub={s:root,r:solved[0]}
 rows=[S.expand(value.subs(sub,simultaneous=True)) for value in eq.values()]
 rows=[value for value in rows if value!=0]
 start=time.monotonic();basis=S.groebner(rows,p,k,extension=S.sqrt(2),order='grevlex')
 result={'sign':sign,'s':str(root),'r':str(solved[0]),'equations':list(map(str,rows)),
         'basis':list(map(str,[poly.as_expr() for poly in basis.polys])),
         'unit':len(basis.polys)==1 and basis.polys[0].as_expr()==1,'seconds':time.monotonic()-start,
         'scope':'ExactCAS on the3x3 coordinate-edge pencil subcase after isolated diagonal zero; not full3x3 chart or Lean theorem.'}
 (out/f'three-by-three-axis-{sign}.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result),flush=True)
