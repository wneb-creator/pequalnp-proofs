from pathlib import Path
from fractions import Fraction
import hashlib,json
import sympy as s
base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
source=base/'star-full-generate-equations.json'
data=json.loads(source.read_text());names=data['unknowns'];variables=s.symbols(names)
for suffix in ['qq','p1009']:
 path=base/f'neogb-star-full-{suffix}.in';meta=json.loads(path.with_suffix('.provenance.json').read_text())
 assert meta['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
 assert meta['input_sha256']==hashlib.sha256(path.read_bytes()).hexdigest()
 assert meta['variables']==names
 tokens=iter(map(int,path.read_text().split()))
 n,m,p,total=[next(tokens) for _ in range(4)]
 assert n==len(names) and m==len(data['equations'])==31 and total==2450
 assert p==(0 if suffix=='qq' else 1009)
 lengths=[next(tokens) for _ in range(m)];assert sum(lengths)==total
 for i,length in enumerate(lengths):
  got={}
  for _ in range(length):
   numerator,denominator=next(tokens),next(tokens);assert denominator>0
   e=tuple(next(tokens) for _ in range(n));assert all(a>=0 for a in e)
   assert e not in got and numerator!=0
   q=Fraction(numerator,denominator)
   got[e]=q if p==0 else q.numerator*pow(q.denominator,-1,p)%p
  expr=s.sympify(data['equations'][i]['coefficient'],locals=dict(zip(names,variables)))
  expected={e:Fraction(q) for e,q in s.Poly(expr,*variables,domain=s.QQ).terms()}
  scaling=meta['equation_scalings'][i]
  factor=Fraction(int(scaling['denominator']),int(scaling['content']))
  assert factor!=0
  if p:
   assert factor.numerator%p and factor.denominator%p
   expected={e:(q*factor).numerator*pow((q*factor).denominator,-1,p)%p for e,q in expected.items()}
   expected={e:q for e,q in expected.items() if q}
  else:expected={e:q*factor for e,q in expected.items()}
  assert got==expected,(suffix,i)
 assert next(tokens,None) is None
 assert meta['generator_count']==m and meta['term_count']==total
 assert meta['dropped_modular_zero_terms']==0
 print(suffix,'PASS',m,'equations',total,'terms; every exact coefficient equals source times recorded nonzero scale')
print('CONVERTER_ACTUAL_INPUTS_PASS')
