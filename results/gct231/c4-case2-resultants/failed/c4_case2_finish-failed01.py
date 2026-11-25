from pathlib import Path
import json
import sympy as S
p=Path(__file__).parent
P,B,U,V,sat=S.symbols('P B U V sat'); loc={str(x):x for x in(P,B,U,V,sat)}
d=json.loads((p/'c4-case2-resultants.json').read_text()); src=d['source']; f=[S.sympify(x,locals=loc) for x in src['equations']]
Q=P**4-2*P**3+4*P+2; W=9*B**2-6*B*P**2-12*B+10*P**2; L=3*B+P**3-2*P**2
r=next(x for x in d['reductions'] if x['label']=='eliminate_V_01')
e=S.Poly(S.rem(S.sympify(r['polynomial'],locals=loc),Q,P),P,B,domain=S.QQ).primitive()[1].as_expr()
a=S.Poly(e,B).coeff_monomial(B)/3
assert S.rem(e-a*L,Q,P)==0
inv,bez,g=S.gcdex(a,Q,P); assert g==1 and S.expand(inv*a+bez*Q-1)==0
assert S.factor(W.subs(B,(2*P**2-P**3)/3))==P**2*Q/3
out={'quartic':str(Q),'W':str(W),'L':str(L),'necessary_remainder_primitive':str(e),'multiplier_a':str(a),'remainder_quotient':str(S.cancel((e-a*L)/Q)),'a_inverse_mod_Q':str(inv),'a_bezout_Q':str(bez),'W_substitution_identity':str(P**2*Q/3),'point_branches':[]}
for bv in (S.Integer(1),S.Rational(16,3)):
 es=[S.factor(x.subs({P:-2,B:bv})) for x in f]; es=[x for x in es if x!=0]
 gb=S.groebner(es,U,V,sat)
 row={'B':str(bv),'equations':[str(x) for x in es],'basis':[str(x.as_expr()) for x in gb.polys]};out['point_branches'].append(row)
 print(row,flush=True)
(p/'c4-case2-finish.json').write_text(json.dumps(out,indent=2)+'\n')
print('All explicit quartic-branch identities verified; final point classification is exactQQ Groebner evidence, not Lean.',flush=True)
