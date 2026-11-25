from pathlib import Path
import sympy as s,json,time
record=json.loads(Path('/tmp/oec/pequalnp-pilot-79/rank2-three-extension.json').read_text());w=s.symbols('w:6');eqs=[s.sympify(f).subs(w[5],0) for f in record['polynomials']];start=time.time()
g=s.groebner(eqs,*w[:5],order='grevlex');print('GB size',len(g.polys),'zero_dimensional',g.is_zero_dimensional,'seconds',time.time()-start,flush=True)
for p in g.polys: print(s.factor(p.as_expr()),flush=True)
