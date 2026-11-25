from fractions import Fraction
from pathlib import Path
import sympy as s,hashlib,json,re,itertools as it,ast
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');f=repo/'ExceptionalCoefficientBridgeFlat.lean';lean=f.read_text();raw=json.loads((job/'geometry-exceptional-raw.json').read_text());cj=json.loads((job/'geometry-exceptional-permanent-correction.json').read_text());ns=cj['variables'];vs=s.symbols(' '.join(ns));z=(0,)*len(vs)
template=Path('fresh_exception_horner_review.py').read_text();exec(template[template.index('def add('):template.index('defs=')].replace('b[0-5]|r|','b[0-5]|r|t|x|'))
defs={n:parse(k) for n,k in re.findall(r'^noncomputable def (raw\d+) [^\n]* := (.*)$',lean,re.M)};target_polys=list(raw['coefficients'].values());assert [defs['raw'+str(i)] for i in range(8)]==[poly(k) for k in target_polys];split=lean.split('noncomputable def fixedT ',1)[1].split('noncomputable def partner ',1)[0].split(':=',1)[1].strip();tr=re.findall(r'!\[([^\[\]]*)\]',split);ts=[parse(y) for row in tr for y in row.split(',')];assert ts==list(map(poly,raw['T']))
line=lean.split('lemma fixed_permanent_expansion',1)[1].split('linear_combination ',1)[1].split('*hQ',1)[0];corr=parse(line);assert corr==poly(cj['quotient'])
one={z:1};vT=poly('t');vX=poly('x');at=poly('(b0+b3+b5+2*(b1+b2+b4)+2)/16');M=[add(one,add(mul(vT,a0),mul(vX,add(poly(k),{m:-c for m,c in at.items()})))) for k,a0 in zip(raw['N'],ts)];F={}
for sig in it.permutations(range(4)):
 e=one
 for i,j in enumerate(sig):e=mul(e,M[4*i+j])
 F=add(F,e)
rawsum={z:24}
for j,k in enumerate(raw['coefficients']):
 i,l=ast.literal_eval(k);rawsum=add(rawsum,mul(defs['raw'+str(j)],poly(f't**{i}*x**{l}')))
assert F==add(rawsum,mul(corr,poly(raw['root_polynomial'])))
# Abstract coefficient extraction.
proof=lean.split('lemma fixed_coefficients',1)[1].split('lemma symmetric_sum_zero',1)[0];basis=s.symbols('f:8');aux=sum(o*s.Symbol('t')**ast.literal_eval(m)[0]*s.Symbol('x')**ast.literal_eval(m)[1] for o,m in zip(basis,raw['coefficients']));ctx={}
for name,t,x in re.findall(r'have (h\d\d) := he \((-?\d+)\) \((-?\d+)\)',proof):ctx[name]=aux.subs({'t':int(t),'x':int(x)})
for i,line in enumerate(re.findall(r'  · linear_combination (.*)$',proof,re.M)):assert not s.expand(s.sympify(line.replace(':ℂ','').replace('^','**'),locals=ctx)-basis[i])
assert len(ctx)==12 and i==7
m=' '.join(lean.split('noncomputable def partner ',1)[1].split('set_option',1)[0].split());assert 'let a : ℂ := (b0+b3+b5+2*(b1+b2+b4)+2)/16 ![![-a,-a,1-a,-a],![-a,b0-a,b1-a,b2-a],![1-a,b1-a,b3-a,b4-a],![-a,b2-a,b4-a,b5-a]]' in m
# For an arbitrary normalized B with sum zero, B = N + B00*J and sumN = 16*a.
assert add(sum((s.Poly(s.sympify(k),*vs) for k in raw['N']),s.Poly(0,*vs)).as_dict(),{m:-16*c for m,c in at.items()})=={}
state=json.loads((repo/'root-ExceptionalCoefficientBridgeFlat-lean-6g-profile-status.json').read_text());sha=hashlib.sha256(f.read_bytes()).hexdigest();assert state['exit_code']==0 and sha==state['sha256']==state['source_sha256_after']
print('PASS actual fixedT and all8 raw definitions; actual correction multiplier times quartic equals exact24-permutation residual; twelve samples extract eight coefficients; normalized partner is N-aJ with sumN=16a. SHA256',sha,'exit0',state['seconds'],'s')
