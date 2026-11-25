from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,ast
import sympy as s
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
data=json.loads((base/'c4-case3-modular-coprime.json').read_text());rows=json.loads((base/'c4-case3-radical-bezout-inputs.json').read_text());b=s.Symbol('beta');poly=lambda z:s.Poly(s.sympify(z,locals={'beta':b,'P':b}),b,domain=s.ZZ)
ps={key:poly(value) for key,value in data.items()}
assert ps['original_f']==poly(rows[0]['radical_other']) and ps['original_g']==poly(rows[1]['radical_other'])
for original,mod,degree in [('original_f','mod_f',67),('original_g','mod_g',85)]:
 assert ps[original].degree()==ps[mod].degree()==degree
 assert ps[original].set_modulus(1009)==ps[mod].set_modulus(1009)
 assert all(0<=int(c)<1009 for c in ps[mod].all_coeffs())
assert (ps['mod_a']*ps['mod_f']+ps['mod_b']*ps['mod_g']-s.Poly(1,b)-1009*ps['integer_quotient']).is_zero
assert s.isprime(1009)
print('Exact reviewed radical lineage, integer/mod1009 maps, exact67/85degrees with nonzero leading residues, and AbarFbar+BbarGbar-1=1009H: PASS',flush=True)
# Parse actual polynomial Horner expressions independently as sparse integer coefficients.
def add(a,c):
 z=dict(a)
 for m,v in c.items():z[m]=z.get(m,0)+v
 return {m:v for m,v in z.items() if v}
def mul(a,c):
 z={}
 for m,v in a.items():
  for n,w in c.items():z[m+n]=z.get(m+n,0)+v*w
 return {m:v for m,v in z.items() if v}
def parse(text):
 def run(t):
  if isinstance(t,ast.Constant):assert isinstance(t.value,int);return {0:t.value} if t.value else {}
  if isinstance(t,ast.Name):assert t.id=='beta';return {1:1}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {m:-v for m,v in run(t.operand).items()}
  if isinstance(t,ast.BinOp):
   if isinstance(t.op,ast.Add):return add(run(t.left),run(t.right))
   if isinstance(t.op,ast.Sub):return add(run(t.left),{m:-v for m,v in run(t.right).items()})
   if isinstance(t.op,ast.Mult):return mul(run(t.left),run(t.right))
  raise AssertionError(ast.dump(t))
 text=text.replace('Polynomial.X','beta')
 return s.Poly.from_dict({(m,):v for m,v in run(ast.parse(text,mode='eval').body).items()},b,domain=s.ZZ)
p=base/'C4Case3ModularCoprime.lean';source=p.read_text();h0=sha(p)
for name,key in [('case3CofactorLeft','original_f'),('case3CofactorRight','original_g'),('case3ModLeft','mod_f'),('case3ModRight','mod_g')]:
 line=next(l for l in source.splitlines() if l.startswith('def '+name+' '));assert parse(line.split(' := ',1)[1])==ps[key]
line=next(l for l in source.splitlines() if l.startswith('  refine ⟨'));parts=line.removeprefix('  refine ⟨').removesuffix('⟩').split(', ');assert len(parts)==3 and parts[2]=='?_' and parse(parts[0])==ps['mod_a'] and parse(parts[1])==ps['mod_b']
line=next(l for l in source.splitlines() if l.startswith('  linear_combination '));expr=line.removeprefix('  linear_combination ').removesuffix(' * hp');assert parse(expr)==ps['integer_quotient']
print('Actual emitted integer and residue polynomial definitions, modular Bezout witnesses and quotient parsed coefficient-for-coefficient: PASS',flush=True)
combined=base/'C4Case3NormModular.lean';co=combined.read_text();h1=sha(combined);generic=(base/'ModularResultantTransfer.lean').read_text();old=(base/'C4Case3Norm.lean').read_text()
for ss in [source,generic]:
 body=ss[ss.index('namespace '):];assert co.count(body)==1
oldproof=old[old.index('    (h0 : '):old.index('  have impossible : ')]
newproof=co[co.index('    (h0 : ',co.index('theorem case3_modular_norm_obstruction')):co.index('  letI : Fact (Nat.Prime 1009)',co.index('theorem case3_modular_norm_obstruction'))]
assert oldproof==newproof
assert '1009 67 85 hd0 hd1 (by decide) hm0 hm1' in co
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',co)
assert h0==sha(p) and h1==sha(combined)
print('Generic transfer and concrete modular bodies copied unchanged; original norm hypotheses/factor/radical reasoning byte-identical. Final application uses explicit degree bounds/exact modular degrees/coprimality and exact original radicals: PASS',flush=True)
print('Hashes',h0,h1,flush=True)
print('Scope: uncompiled source review for conditional two-norm obstruction only. Combined scratch has multiple namespaces; named-file integration must place helpers in one outer block and deduplicate common-root helper. No characteristic-zero assertion from a modular unit without degree checks.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
