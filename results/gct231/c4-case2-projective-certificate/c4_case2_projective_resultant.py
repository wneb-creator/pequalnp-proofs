from pathlib import Path
import json,time
import sympy as S
p=Path(__file__).parent
P,B,U,V=S.symbols('P B U V'); loc={str(x):x for x in(P,B,U,V)}
d=json.loads((p/'c4-case2-resultants.json').read_text()); source=d['source']; F=S.sympify(d['scale_curve'],locals=loc); K=P**2+P-1
rs={x['label']:S.sympify(x['polynomial'],locals=loc) for x in d['reductions']};q=rs['q'];c=rs['c'];r=rs['linear_r'];l=rs['quadratic_l'];a=S.diff(r,U)
field=S.QQ.frac_field(P,U,V);modulus=S.Poly(F,B,domain=field)
start=time.monotonic();out=[]
first={}
for label,poly in [('q',q),('c',c),('l',l)]:
 first[label]=S.resultant(r,poly,U);print('first',label,len(S.Poly(first[label],P,B,V).terms()),time.monotonic()-start,flush=True)
for x,y,power in [('q','l',4),('q','c',6)]:
 raw=S.resultant(first[x],first[y],V);print('raw',x+y,len(S.Poly(raw,P,B).terms()),time.monotonic()-start,flush=True)
 divided=S.Poly(raw,P,B,domain=S.QQ).exquo(S.Poly(a**power,P,B,domain=S.QQ)).as_expr()
 print('divided',x+y,len(S.Poly(divided,P,B).terms()),S.Poly(divided,P,B).total_degree(),time.monotonic()-start,flush=True)
 rem=S.cancel(S.rem(S.Poly(divided,B,domain=field),modulus).as_expr());num,den=S.fraction(rem);num=S.Poly(num,P,B,domain=S.QQ).primitive()[1].as_expr()
 row={'pair':[x,y],'power':power,'quotient':str(divided),'curve_reduced_numerator':str(num),'curve_denominator':str(den)};out.append(row)
 print('reduced',x+y,len(S.Poly(num,P,B).terms()),S.Poly(num,P,B).total_degree(),time.monotonic()-start,flush=True)
 (p/'c4-case2-projective-resultants.json').write_text(json.dumps(out,indent=2)+'\n')
