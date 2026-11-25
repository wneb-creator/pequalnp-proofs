from pathlib import Path
import json,time
import sympy as S
p=Path(__file__).parent;P,B=S.symbols('P B');loc={'P':P,'B':B}
base=json.loads((p/'c4-case2-resultants.json').read_text());F=S.Poly(S.sympify(base['scale_curve'],locals=loc),B);fa,fb,fc=[S.Poly(x,P,domain=S.QQ) for x in F.all_coeffs()];K=S.Poly(P**2+P-1,P);Q=S.Poly(P**4-2*P**3+4*P+2,P)
rows=json.loads((p/'c4-case2-projective-resultants.json').read_text())+json.loads((p/'c4-case2-projective-resultants-qc.json').read_text());norms=[];out=[];start=time.monotonic()
for row in rows:
 r=S.Poly(S.sympify(row['curve_reduced_numerator'],locals=loc),B);a,c=[S.Poly(x,P,domain=S.QQ) for x in r.all_coeffs()];n=(fa*c*c-fb*a*c+fc*a*a).primitive()[1];removed=[]
 for safe in [S.Poly(P,P),K]:
  while True:
   quo,rem=n.div(safe)
   if not rem.is_zero:break
   n=quo;removed.append(str(safe.as_expr()))
 norms.append(n);out.append({'pair':row['pair'],'norm':str(n.as_expr()),'removed':removed});print(row['pair'],n.degree(),time.monotonic()-start,flush=True)
g=norms[0].gcd(norms[1]);print('gcd',S.factor(g.as_expr()),flush=True)
a,b=norms[0].exquo(g),norms[1].exquo(g);A,C,D=S.gcdex(a,b);assert D==S.Poly(1,P,domain=S.QQ);assert A*a+C*b==D
coeffs=A.all_coeffs()+C.all_coeffs();den=S.ilcm(*[x.q for x in coeffs]);Ai=A.mul_ground(den);Ci=C.mul_ground(den)
cert={'gcd':str(g.as_expr()),'gcd_factor':str(S.factor(g.as_expr())),'scale':str(den),'first_multiplier':str(Ai.as_expr()),'second_multiplier':str(Ci.as_expr()),'first_cofactor':str(a.as_expr()),'second_cofactor':str(b.as_expr())}
print('bezout sizes',len(cert['first_multiplier']),len(cert['second_multiplier']),len(str(den)),flush=True)
(p/'c4-case2-projective-norms.json').write_text(json.dumps({'norms':out,'certificate':cert},indent=2)+'\n')
