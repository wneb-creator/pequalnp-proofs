import argparse,json,hashlib
from pathlib import Path
import sympy as s
parser=argparse.ArgumentParser(description='Convert chart equations to characteristic-zero OpenF4 input with signed integer coefficients.')
parser.add_argument('json');parser.add_argument('output');a=parser.parse_args()
src=Path(a.json);data=json.loads(src.read_text());names=data['unknowns'];xs=s.symbols(names);out=[];scalings=[]
for record in data['equations']:
 poly=s.Poly(s.sympify(record['coefficient'],locals=dict(zip(names,xs))),*xs,domain=s.QQ)
 den,integer=poly.clear_denoms();content,integer=integer.primitive()
 terms=[]
 for powers,coef in integer.terms():
  c=int(coef)
  if not c:continue
  term=str(c)+''.join('*'+name+('^'+str(e) if e!=1 else '') for name,e in zip(names,powers) if e)
  if terms and c>0:term='+'+term
  terms.append(term)
 if terms:out.append(''.join(terms));scalings.append({'denominator':str(den),'content':str(content)})
text='0 '+str(len(names))+' '+str(len(out))+'\n'+' '.join(names)+'\n'+'\n'.join(out)+'\n'
dst=Path(a.output);dst.write_text(text)
meta={'source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'characteristic':0,'variables':names,'equation_count':len(out),'equation_scalings':scalings,'input_sha256':hashlib.sha256(dst.read_bytes()).hexdigest()}
dst.with_suffix('.provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({k:v for k,v in meta.items() if k not in ('variables','equation_scalings')}))
