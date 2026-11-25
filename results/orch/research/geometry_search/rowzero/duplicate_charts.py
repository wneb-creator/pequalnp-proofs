import sympy as S,itertools,time,json
from pathlib import Path

h,k,r,t,u=S.symbols('h k r t u')
variables=(h,k,r,t,u)
polys=[S.sympify(line,locals=dict(zip(('h','k','r','t','u'),variables))) for line in Path('/tmp/oec/pequalnp-pilot-78/construct_search/duplicate-row-polynomials.txt').read_text().splitlines()]
P=S.Matrix([[1,-1,S.Rational(1,32),S.Rational(1,192),0],[-2,1,S.Rational(-1,16),S.Rational(-17,192),S.Rational(-1,3)],[0,-1,0,S.Rational(5,192),S.Rational(1,3)],[0,1,0,S.Rational(-1,192),S.Rational(-1,3)],[0,-3,S.Rational(1,8),S.Rational(11,192),1]])
x1,x2,y1,y2,z=S.symbols('x1 x2 y1 y2 z')
coords=S.Matrix([x1,x2,y1,y2,z])
converted=[S.expand(p.subs(dict(zip(variables,P*coords)))) for p in polys]
assert S.expand(converted[0]-x1*y1-x2*y2-S.Rational(8,9)*z*z)==0
A,B,K,s,v=S.symbols('A B K s v')
Z=A*s+B*v
Y1=-S.Rational(8,9)*A*Z+K*v
Y2=-S.Rational(8,9)*B*Z-K*s
for flip in itertools.product([0,1],repeat=2):
 print('CHART',flip,'START',time.time(),flush=True)
 sub={x1:Y1 if flip[0] else s,y1:s if flip[0] else Y1,
      x2:Y2 if flip[1] else v,y2:v if flip[1] else Y2,z:Z}
 eq=[]
 for p in converted[1:]:
  for co in S.Poly(S.expand(p.subs(sub)),s,v).coeffs():
   q=S.Poly(co,A,B,K).clear_denoms()[1].primitive()[1].as_expr()
   eq.append(q)
 print('EQUATIONS',len(eq),'MAXDEG',max(S.Poly(e,A,B,K).total_degree() for e in eq),flush=True)
 Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/duplicate_eq_'+''.join(map(str,flip))+'.json').write_text(json.dumps([str(e) for e in eq],indent=2))
 G=S.groebner(eq,A,B,K,order='grevlex',method='f5b')
 print('GROEBNER',G,flush=True)
 if list(G)==[1]:continue
 print('ZERO DIMENSIONAL',G.is_zero_dimensional,flush=True)
 if G.is_zero_dimensional:
  L=G.fglm('lex')
  print('LEX',L,flush=True)
  print('SOLUTIONS',S.solve_poly_system(list(L),A,B,K),flush=True)
 else:
  for e in G.polys:print(S.factor(e.as_expr()),flush=True)
