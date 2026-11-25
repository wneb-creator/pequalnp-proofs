import argparse,json,hashlib
from pathlib import Path
import sympy as s
ap=argparse.ArgumentParser(description='Convert reviewed chart equations to neogb sparse array input.')
ap.add_argument('json');ap.add_argument('output');ap.add_argument('--characteristic',type=int,default=1009);a=ap.parse_args()
assert a.characteristic==0 or s.isprime(a.characteristic)
src=Path(a.json);data=json.loads(src.read_text());names=data['unknowns'];u=s.symbols(names);polys=[];lens=[];scalings=[];dropped=0
for item in data['equations']:
 f=s.Poly(s.sympify(item['coefficient'],locals=dict(zip(names,u))),*u,domain=s.QQ)
 den,f=f.clear_denoms();content,f=f.primitive();terms=[]
 for exps,coeff in f.terms():
  coeff=int(coeff)
  if a.characteristic and coeff%a.characteristic==0:dropped+=1;continue
  terms.append((coeff,tuple(int(e) for e in exps)))
 if terms:
  lens.append(len(terms));polys.extend(terms);scalings.append({'denominator':str(den),'content':str(content)})
text=f'{len(names)} {len(lens)} {a.characteristic} {len(polys)}\n'+' '.join(map(str,lens))+'\n'+''.join(str(c)+' 1 '+' '.join(map(str,e))+'\n' for c,e in polys)
dst=Path(a.output);dst.write_text(text)
meta={'source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'characteristic':a.characteristic,'variables':names,'generator_count':len(lens),'term_count':len(polys),'dropped_modular_zero_terms':dropped,'equation_scalings':scalings,'input_sha256':hashlib.sha256(dst.read_bytes()).hexdigest()}
dst.with_suffix('.provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k not in ('variables','equation_scalings')}),flush=True)
