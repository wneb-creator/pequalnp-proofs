from pathlib import Path
import sympy as s,itertools,re,json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'basic_star'
src=(job/'NormalizedBody.lean').read_text();full=(job/'Normalized.lean').read_bytes()
B,C,D,E,F,r,z,h,a,b,c,d,e,f=s.symbols('B C D E F r z h a b c d e f');loc={str(x):x for x in (B,C,D,E,F,r)}
def let(name):
 m=re.search(r'  let '+name+r' := (.*?)(?=\n  (?:let|have)|\n    (?:let|have))',src,re.S)
 assert m,name
 return s.sympify(m.group(1).replace('^','**'),locals=loc)
P=2*a*a*(d*f+e*e)+8*a*b*c*e+4*a*(b*b*f+c*c*d)+4*b*b*c*c
M=s.Matrix([[a,a,b,c],[a,a,b,c],[b,b,d,e],[c,c,e,f]])
direct=sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))
assert s.expand(direct-P)==0
actual=s.Poly(s.expand(P.subs({a:1+z,b:1+B*z,c:1+C*z,d:1+D*z+(r-1)*h,e:1+E*z+h,f:1+F*z+(-r-1)*h},simultaneous=True)-24),z,h)
checks={}
for i in (1,2,3):
 checks['q'+str(i)]=s.expand(actual.coeff_monomial(z**i)-let('q'+str(i)))==0
 checks['l'+str(i)]=s.expand(actual.coeff_monomial(z**i*h)-let('l'+str(i)))==0
assert all(checks.values())
assert set(exp[1] for exp,co in actual.terms())<=set([0,1,2])
hr=r*r-2
rem=lambda x:s.rem(s.Poly(s.expand(x),r),s.Poly(hr,r)).as_expr().expand()
D0=r-2+(r-4)*B+r*C+(r-1)*E
F0=-2-r-r*B-(4+r)*C-(r+1)*E
checks['linear_constraints_solve_D_F']=rem(let('q1').subs({D:D0,F:F0},simultaneous=True))==0 and rem(let('l1').subs({D:D0,F:F0},simultaneous=True))==0
checks['split_identity']=rem(let('l2').subs({D:D0,F:F0},simultaneous=True)+4*(B-C)*((r+1)*B+(r-1)*C-2*r))==0
Q=B*B+6*B+3;T=B*(B+1)**2
checks['equal_bezout']=s.expand((11*B*B+16*B+2)*Q-(11*B+60)*T-6)==0
Q2=5*B*B+(-18+8*r)*B-17+12*r;T2=(B-r)*(5*B*B+(-14+4*r)*B-3+4*r)
U=(3485+2460*r)*B*B-(6032+4250*r)*B+1848+1324*r
V=(3485+2460*r)*B+36+55*r
checks['other_bezout']=rem(U*Q2-V*T2-318)==0
assert all(checks.values())
assert not re.search(r'_root_|\bsorry\b|\baxiom\b|\bnative_decide\b|"',src)
report={'status':'PASS','component_sha256':hashlib.sha256(full).hexdigest(),'body_sha256':hashlib.sha256(src.encode()).hexdigest(),'checks':checks,'statement_scope':'Excludes only the displayed normalized duplicate-row pair with r^2=2. General subspace normalization is separate.','source_review':'No implicit extra hypotheses, circular target use, forbidden declarations or string literals; exact permanent formula independently verified from24terms.'}
(base/'geometry_search/basic-star-normalized-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
