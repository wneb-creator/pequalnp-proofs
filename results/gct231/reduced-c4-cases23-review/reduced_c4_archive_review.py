from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,json
import sympy as s

base=Path('/workspace/pequalnp-proofs/results/gct231/reduced-c4-cases23')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
manifest=base/'sha256.json'
assert sha(manifest)=='f69462cd385f0026718b2a01e56969f3190680f7d72ac15039f5b62375203c90'
expected=json.loads(manifest.read_text())
files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=manifest}
assert set(files)==set(expected) and len(files)==46
for name,p in files.items():
 assert not p.is_symlink() and sha(p)==expected[name],name
 raw=p.read_bytes();raw.decode('utf8');assert b'\x00' not in raw
 assert not raw.startswith((b'\x7fELF',b'MZ',b'PK\x03\x04'))
print('Exact46-file manifest coverage, all hashes, regularUTF8/nonbinary: PASS',flush=True)
root_values={2:[-2,1,0,6,s.Rational(-1,26)],3:[4,s.Rational(1,2),0,-12,s.Rational(1,13)]}
source_hashes={2:'0ab9ffa48a2b21f637556a635ff1f835fd59836ad48c77cec594a1751f7dc87b',3:'72b12e2f543766e57aec78a88717f5133442553a207566956022363aa89a867f'}
for case in (2,3):
 source=base/f'c4-nonzero-reduced-{case}.json';normal=base/f'c4-nonzero-reduced-{case}-normalized.json'
 assert sha(source)==source_hashes[case]
 d=json.loads(source.read_text());nd=json.loads(normal.read_text())
 assert nd['unknowns']==d['variables']
 assert [p['coefficient'] for p in nd['equations']]==d['equations']
 assert nd['normalized_source_sha256']==sha(source)
 variables=s.symbols(d['variables']);loc=dict(zip(d['variables'],variables))
 parse=lambda text:s.sympify(text,locals=loc)
 polynomials=[s.Poly(parse(expr),*variables,domain=s.QQ) for expr in d['equations']]
 point=dict(zip(variables,root_values[case]))
 assert all(p.as_expr().subs(point)==0 for p in polynomials)
 print('CASE',case,'exact rational root of all6 original equations: PASS',flush=True)
 for label,characteristic in [('qq',0),('p1009',1009)]:
  inp=base/f'neogb-c4-reduced{case}-{label}.in'
  prov=json.loads((base/f'neogb-c4-reduced{case}-{label}.provenance.json').read_text())
  assert prov['source_sha256']==sha(normal) and prov['input_sha256']==sha(inp)
  tokens=list(map(int,inp.read_text().split()));n,m,p,total=tokens[:4]
  assert n==5 and m==6 and p==characteristic
  lengths=tokens[4:10];assert sum(lengths)==total
  pos=10
  for i,(length,original) in enumerate(zip(lengths,polynomials)):
   got={}
   for _ in range(length):
    num,den=tokens[pos:pos+2];mon=tuple(tokens[pos+2:pos+7]);pos+=7
    assert len(mon)==5 and all(e>=0 for e in mon) and mon not in got and den>0
    got[mon]=Fraction(num,den) if p==0 else num*pow(den,-1,p)%p
   denom,integral=original.clear_denoms();content,primitive=integral.primitive()
   scaling=prov['equation_scalings'][i]
   assert s.Rational(scaling['denominator'])/s.Rational(scaling['content'])==denom/content
   want={mon:Fraction(int(c.p),int(c.q)) for mon,c in primitive.terms()}
   if p:
    assert int(denom)%p and int(content)%p
    want={mon:c.numerator*pow(c.denominator,-1,p)%p for mon,c in want.items()}
    want={mon:c for mon,c in want.items() if c}
   assert got==want,(case,label,i)
  assert pos==len(tokens)
  print('CASE',case,label,'all6 input rows independently match source primitive polynomials',flush=True)
 qqmeta=json.loads((base/f'neogb-c4-reduced{case}-qq-r1.result.json').read_text())
 assert qqmeta['status']=='UNKNOWN_TIME_LIMIT' and qqmeta['returncode'] is None
 assert qqmeta['wall_limit_seconds']==120 and qqmeta['memory_mib']==1024
 assert qqmeta['input_sha256']==sha(base/f'neogb-c4-reduced{case}-qq.in')
 assert not (base/f'neogb-c4-reduced{case}-qq-r1-basis.json').exists()
 ffmeta=json.loads((base/f'neogb-c4-reduced{case}-native-p1009-r1.result.json').read_text())
 basisfile=base/f'neogb-c4-reduced{case}-native-p1009-r1-basis.json'
 assert ffmeta['status']=='COMPLETED' and ffmeta['returncode']==0 and not ffmeta['unit_basis']
 assert ffmeta['basis_size']==5 and ffmeta['threads']==1
 assert ffmeta['input_sha256']==sha(base/f'neogb-c4-reduced{case}-p1009.in')
 assert ffmeta['output_sha256']==sha(basisfile)
 basis=json.loads(basisfile.read_text())
 assert basis['characteristic']==1009 and basis['nvars']==5 and basis['nterms']==9
 expressions=[sum(s.Integer(co)*s.prod(v**e for v,e in zip(variables,mon)) for co,mon in row) for row in basis['basis']]
 assert all(s.Poly(expr,*variables).total_degree()==1 for expr in expressions)
 matrix=s.Matrix([[expr.coeff(v) for v in variables] for expr in expressions])
 assert int(matrix.det())%1009!=0
 modular_point={v:int(s.numer(val))*pow(int(s.denom(val)),-1,1009)%1009 for v,val in point.items()}
 assert all(int(expr.subs(modular_point))%1009==0 for expr in expressions)
 assert all(int(p.clear_denoms()[1].as_expr().subs(modular_point))%1009==0 for p in polynomials)
 print('CASE',case,'completed nonunit linearFF basis/root and QQ120s UNKNOWN interpretation: PASS',flush=True)

 # Check the omitted square condition at both algebraic lifts of the reduced point.
 original=json.loads((Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')/f'c4-nonzero-square-{case}.json').read_text())
 alpha,beta,gamma,u,v=s.symbols('alpha beta gamma u v')
 ns={str(z):z for z in (alpha,beta,gamma,u,v)}
 sq=s.sympify(original['equations'][4],locals=ns)
 for sign in (-1,1):
  lift={alpha:-2/sign,beta:sign,gamma:-s.Rational(1,2),u:0,v:6/sign} if case==2 else {alpha:2*sign,beta:s.Rational(1,2),gamma:sign,u:0,v:-6*sign}
  lift={key:s.Rational(value) for key,value in lift.items()}
  obstruction=s.expand(sq.subs(lift))
  assert obstruction!=0
  print('CASE',case,'square-condition obstruction at lift sign',sign,obstruction,flush=True)
print('No solver rerun; rational roots do not classify all complex solutions',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
