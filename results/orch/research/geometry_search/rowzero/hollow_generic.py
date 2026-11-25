import sympy as S,time
from pathlib import Path
A,B,K=S.symbols('A B K')
lines=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero/hollow_chart.stdout').read_text().splitlines()
eq=[S.sympify(l.split(') ',1)[1],locals={'A':A,'B':B,'K':K}) for l in lines if l.startswith('COEFF ')]
eq[0]=S.cancel(eq[0]/(A+1))
eq[3]=S.cancel(eq[3]/(B+1))
print('START',time.time(),flush=True)
G=S.groebner(eq,A,B,K,order='grevlex',method='f5b')
print('GB',G,flush=True)
for p in G.polys:print(S.factor(p.as_expr()),flush=True)
print('ZERO DIMENSIONAL',G.is_zero_dimensional,flush=True)
if G.is_zero_dimensional:
 L=G.fglm('lex')
 print('LEX',L,flush=True)
 for p in L.polys:print(S.factor(p.as_expr()),flush=True)
 print('SOLUTIONS',S.solve_poly_system(list(L),A,B,K),flush=True)
