from pathlib import Path
import json,time
import sympy as S
p=Path(__file__).parent
P,B,U,V=S.symbols('P B U V'); loc={str(x):x for x in (P,B,U,V)}
d=json.loads((p/'c4-case2-resultants.json').read_text()); F=S.sympify(d['scale_curve'],locals=loc); K=P**2+P-1
fa,fb,fc=S.Poly(F,B).all_coeffs(); common=None; out=[]; start=time.monotonic()
for r in d['reductions']:
 if not r['label'].startswith('eliminate_V'): continue
 f=S.Poly(S.sympify(r['polynomial'],locals=loc),B)
 assert f.degree()==1
 a,c=f.all_coeffs(); norm=S.Poly(S.expand(fa*c*c-fb*a*c+fc*a*a),P,domain=S.QQ).primitive()[1]
 removed=[]
 for safe in [S.Poly(P,P),S.Poly(K,P)]:
  while True:
   q,rem=norm.div(safe)
   if not rem.is_zero: break
   norm=q; removed.append(str(safe.as_expr()))
 common=norm if common is None else common.gcd(norm)
 row={'label':r['label'],'norm':str(norm.as_expr()),'removed_nonzero_factors':removed,'gcd_so_far':str(common.as_expr())}; out.append(row)
 print(r['label'],'normdegree',norm.degree(),'gcddegree',common.degree(),'seconds',time.monotonic()-start,flush=True)
 (p/'c4-case2-norm-gcd.json').write_text(json.dumps(out,indent=2)+'\n')
print('factor_final_gcd',S.factor(common.as_expr()),flush=True)
