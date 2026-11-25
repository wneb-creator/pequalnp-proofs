from pathlib import Path
import json,sympy as s
r=Path(__file__).parent;b=s.symbols('beta');rows=json.loads((r/'c4-case3-squarefree.json').read_text());data=json.loads((r/'c4-case3-bezout-inputs.json').read_text());ps=[];out=[]
for row in rows:
 p=s.Poly(1,b,domain=s.QQ);fs=[];allf=s.Poly(1,b,domain=s.QQ)
 for entry in row['factors']:
  f=s.Poly(s.sympify(entry['polynomial'],locals={'beta':b}),b,domain=s.QQ).primitive()[1];n=entry['multiplicity'];allf*=f**n
  fs.append({'polynomial':str(f.as_expr()),'multiplicity':n})
  if f.degree()>1:p*=f
 p=p.primitive()[1];ps.append(p);ratio=s.Poly(s.sympify(data[row['key']],locals={'beta':b}),b,domain=s.QQ).exquo(allf)
 assert ratio.degree()==0
 out.append({'key':row['key'],'factors':fs,'factor_scale':str(ratio.as_expr()),'radical_other':str(p.as_expr())})
assert s.gcd(ps[0],ps[1]).degree()==0
lines=[]
for poly in ps:
 lines.append(str(poly.degree()+1))
 for c in reversed(poly.all_coeffs()):lines.append(str(c.p)+' '+str(c.q))
(r/'c4-case3-radical-bezout.in').write_text('\n'.join(lines)+'\n')
(r/'c4-case3-radical-bezout-inputs.json').write_text(json.dumps(out,indent=2)+'\n')
print('coprime radical degrees',*[p.degree() for p in ps],flush=True)
