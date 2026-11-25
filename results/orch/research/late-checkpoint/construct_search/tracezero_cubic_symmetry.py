from pathlib import Path
import sympy as s,json,resource,time
from sympy.polys.matrices import DomainMatrix
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20));resource.setrlimit(resource.RLIMIT_CPU,(30,35))
b=Path('/tmp/oec/pequalnp-pilot-78/construct_search');a,bb,c,d,e,f,x,y,z=s.symbols('a b c d e f x y z');v=[a,bb,d,e,f,x,y,z];q,C,_=[s.sympify(t) for t in (b/'hadamard-polynomials.txt').read_text().splitlines()];C=s.expand(C.subs(c,-a-bb));q=s.expand(q.subs(c,-a-bb));columns=[s.Poly(s.expand(s.diff(C,vi)*vj),*v) for vi in v for vj in v];monos=sorted(set(m for p in columns for m,co in p.terms()));M=s.Matrix([[p.coeff_monomial(m) for p in columns] for m in monos]);start=time.monotonic();N=DomainMatrix.from_Matrix(M).convert_to(s.QQ).nullspace().to_Matrix();print('CUBIC_LIE_ALGEBRA_DIM',N.rows,'SECONDS',time.monotonic()-start,flush=True)
if N.rows:
 eq=[]
 for row in N.tolist():
  A=s.Matrix(8,8,row);expr=s.Poly(s.expand(sum(s.diff(q,v[i])*A[i,j]*v[j] for i in range(8) for j in range(8))),*v);eq.append(expr)
 mons=sorted(set(m for p in eq for m,c in p.terms()));K=s.Matrix([[p.coeff_monomial(m) for p in eq] for m in mons]);print('PAIR_LIE_DIM',N.rows-K.rank(),flush=True)
(b/'tracezero-cubic-symmetry.json').write_text(json.dumps({'variables':list(map(str,v)),'cubic_lie_dimension':N.rows,'generators':[[str(c) for c in row] for row in N.tolist()]}))
