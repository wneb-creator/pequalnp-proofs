import sympy as S,time
from pathlib import Path
h,k,r,t,u=S.symbols('h k r t u')
vs=(h,k,r,t,u)
polys=[S.sympify(l,locals=dict(zip(('h','k','r','t','u'),vs))) for l in Path('/tmp/oec/pequalnp-pilot-78/construct_search/duplicate-row-polynomials.txt').read_text().splitlines()]
for name,sub,unknowns in [
 ('middle_diag_one',{r:1,u:-4*h-2*k-4-4*t},(h,k,t)),
 ('middle_diag_zero_last_one',{r:0,u:1,k:S.Rational(-1,2)-2*h-2*t},(h,t))]:
 es=[S.factor(S.expand(p.subs(sub,simultaneous=True))) for p in polys]
 print('CHART',name,'START',time.time(),flush=True)
 for e in es:print('EQUATION',e,flush=True)
 G=S.groebner(es,*unknowns,order='grevlex',method='f5b')
 print('GB',G,flush=True)
 if list(G)==[1]:continue
 print('ZERO DIMENSIONAL',G.is_zero_dimensional,flush=True)
 if G.is_zero_dimensional:
  L=G.fglm('lex')
  print('LEX',L,flush=True)
  for e in L.polys:print('FACTOR',S.factor(e.as_expr()),flush=True)
  print('SOLUTIONS',S.solve_poly_system(list(L),*unknowns),flush=True)
