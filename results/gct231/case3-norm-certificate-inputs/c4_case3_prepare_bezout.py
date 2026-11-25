from pathlib import Path
import hashlib,json,sympy as s
r=Path(__file__).parent; b=s.symbols('beta'); loc={'beta':b}
fwd=json.loads((r/'c4-case3-norm-gcd.json').read_text()); rev=json.loads((r/'c4-case3-reverse-firstnorm.json').read_text())
f=s.Poly(s.sympify(fwd[1]['norm'],locals=loc),b,domain=s.QQ).primitive()[1]
g=s.Poly(s.sympify(rev['norm'],locals=loc),b,domain=s.QQ).primitive()[1]
h=s.gcd(f,g); a=f.exquo(h); c=g.exquo(h)
assert h.monic()==s.Poly((b+2)**22*(2*b-1)**24,b,domain=s.QQ).monic()
data={'sources':{'c4-case3-norm-gcd.json':hashlib.sha256((r/'c4-case3-norm-gcd.json').read_bytes()).hexdigest(),'c4-case3-reverse-firstnorm.json':hashlib.sha256((r/'c4-case3-reverse-firstnorm.json').read_bytes()).hexdigest()},'forward_index':1,'first_norm':str(f.as_expr()),'second_norm':str(g.as_expr()),'gcd':str(h.as_expr()),'gcd_factor':str(s.factor(h.as_expr())),'first_cofactor':str(a.as_expr()),'second_cofactor':str(c.as_expr())}
(r/'c4-case3-bezout-inputs.json').write_text(json.dumps(data,indent=2)+'\n')
lines=[]
for poly in [a,c]:
 lines.append(str(poly.degree()+1))
 for z in reversed(poly.all_coeffs()):lines.append(str(z.p)+' '+str(z.q))
(r/'c4-case3-bezout.in').write_text('\n'.join(lines)+'\n')
print(json.dumps({'norm_degrees':[f.degree(),g.degree()],'cofactor_degrees':[a.degree(),c.degree()],'gcd_factor':data['gcd_factor']}),flush=True)
