from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,json
import sympy as s
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
expected={2:'0ab9ffa48a2b21f637556a635ff1f835fd59836ad48c77cec594a1751f7dc87b',3:'72b12e2f543766e57aec78a88717f5133442553a207566956022363aa89a867f'}
print('Generator source SHA256',sha(root/'reduced_c4_saturate_U.py'),flush=True)
for case in (2,3):
 old=root/'fresh'/f'c4-nonzero-reduced-{case}.json'
 source=root/f'c4-nonzero-U-saturated-{case}.json'
 normal=root/f'c4-nonzero-U-saturated-{case}-normalized.json'
 assert sha(old)==expected[case]
 a=json.loads(old.read_text());d=json.loads(source.read_text());nd=json.loads(normal.read_text())
 assert d['variables']==a['variables']+['invU']
 assert d['equations'][:6]==a['equations'] and len(d['equations'])==7
 assert d['reduced_source_sha256']==sha(old)
 assert nd['unknowns']==d['variables'] and nd['normalized_source_sha256']==sha(source)
 assert [p['coefficient'] for p in nd['equations']]==d['equations']
 vs=s.symbols(d['variables']);loc=dict(zip(d['variables'],vs))
 polys=[s.Poly(s.sympify(t,locals=loc),*vs,domain=s.QQ) for t in d['equations']]
 assert s.expand(polys[6].as_expr()-loc['invU']*loc['U']+1)==0
 print('CASE',case,'exact six-equation prefix and appended invU*U-1: PASS; source SHA256',sha(source),flush=True)
 for label,characteristic in [('qq',0),('p1009',1009)]:
  inp=root/f'neogb-c4-Usaturated{case}-{label}.in'
  prov=json.loads((root/f'neogb-c4-Usaturated{case}-{label}.provenance.json').read_text())
  assert prov['source_sha256']==sha(normal) and prov['input_sha256']==sha(inp)
  assert prov['variables']==d['variables'] and prov['characteristic']==characteristic
  assert prov['generator_count']==7
  tok=list(map(int,inp.read_text().split()));n,m,p,total=tok[:4]
  assert (n,m,p)==(6,7,characteristic)
  lengths=tok[4:11];assert sum(lengths)==total==prov['term_count']
  pos=11
  for i,(length,poly) in enumerate(zip(lengths,polys)):
   got={}
   for _ in range(length):
    num,den=tok[pos:pos+2];mon=tuple(tok[pos+2:pos+8]);pos+=8
    assert den>0 and all(e>=0 for e in mon) and mon not in got
    if i<6:assert mon[-1]==0
    got[mon]=Fraction(num,den) if p==0 else num*pow(den,-1,p)%p
   denominator,integral=poly.clear_denoms();content,primitive=integral.primitive()
   scaling=prov['equation_scalings'][i]
   assert s.Rational(scaling['denominator'])/s.Rational(scaling['content'])==denominator/content
   want={mon:Fraction(int(c.p),int(c.q)) for mon,c in primitive.terms()}
   if p:
    assert int(denominator)%p and int(content)%p
    want={mon:c.numerator*pow(c.denominator,-1,p)%p for mon,c in want.items()}
    want={mon:c for mon,c in want.items() if c}
   assert got==want,(case,label,i)
  assert pos==len(tok)
  print('CASE',case,label,'all seven sparse rows verified; total terms',total,'input SHA256',sha(inp),flush=True)
print('Over C, a point of the original reduced system with U!=0 lifts uniquely by invU=1/U. Thus a characteristic-zero unit certificate would imply U=0 for that reduced system. No solver verdict or finite-field-to-C inference.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
