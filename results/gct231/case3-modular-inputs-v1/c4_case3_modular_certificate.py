from pathlib import Path
import json,sympy as s,hashlib,time
r=Path(__file__).parent;b=s.symbols('beta');data=json.loads((r/'c4-case3-radical-bezout-inputs.json').read_text());start=time.monotonic();p=1009
f,g=[s.Poly(s.sympify(x['radical_other'],locals={'beta':b}),b,domain=s.QQ) for x in data];ff,gg=[s.Poly(x.as_expr(),b,modulus=p) for x in[f,g]]
A,B,h=s.gcdex(ff,gg);assert h==s.Poly(1,b,modulus=p);assert A*ff+B*gg==h
out={'prime':p,'source_sha256':hashlib.sha256((r/'c4-case3-radical-bezout-inputs.json').read_bytes()).hexdigest(),'first_integer_polynomial':str(f.as_expr()),'second_integer_polynomial':str(g.as_expr()),'first_modular_polynomial':str(ff.as_expr()),'second_modular_polynomial':str(gg.as_expr()),'first_multiplier':str(A.as_expr()),'second_multiplier':str(B.as_expr()),'degrees':[f.degree(),g.degree(),ff.degree(),gg.degree()],'leading_coefficients_mod_p':[int(ff.LC())%p,int(gg.LC())%p]}
(r/'c4-case3-modular-certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'EXACT_FINITE_FIELD_BEZOUT','degrees':out['degrees'],'leading_coefficients_mod_p':out['leading_coefficients_mod_p'],'wall_seconds':time.monotonic()-start}),flush=True)
