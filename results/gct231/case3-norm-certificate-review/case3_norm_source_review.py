from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,ast
import sympy as s
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
p=base/'C4Case3Norm.lean';src=p.read_text();assert sha(p)=='04875a577df9d5bae7e4cb1520c779fa24d7978de79adddbe4dbfd023ad5813f'
d=json.loads((base/'c4-case3-bezout-inputs.json').read_text());rows=json.loads((base/'c4-case3-radical-bezout-inputs.json').read_text());cert=json.loads((base/'c4-case3-radical-modular-bezout.integer-certificate.json').read_text());b=s.Symbol('beta');poly=lambda t:s.Poly(s.sympify(t,locals={'beta':b}),b,domain=s.QQ)
for name,h in d['sources'].items():assert sha(base/name)==h
forward=json.loads((base/'c4-case3-norm-gcd.json').read_text());reverse=json.loads((base/'c4-case3-reverse-firstnorm.json').read_text())
assert d['forward_index']==1 and poly(d['first_norm'])==poly(forward[1]['norm']) and poly(d['second_norm'])==poly(reverse['norm'])
D=int(cert['scale']);assert D!=0
A=s.Poly.from_list(list(reversed(list(map(int,cert['first_multiplier'])))),b,domain=s.ZZ);B=s.Poly.from_list(list(reversed(list(map(int,cert['second_multiplier'])))),b,domain=s.ZZ)
radicals=[]
for row,key in zip(rows,['first_norm','second_norm']):
 assert row['key']==key and row['factor_scale']=='-1'
 factors=[poly(x['polynomial']) for x in row['factors']];powers=[x['multiplicity'] for x in row['factors']];prod=s.Poly(-1,b,domain=s.QQ)
 for f,n in zip(factors,powers):prod*=f**n
 assert prod==poly(d[key]);assert factors[2]==poly('beta+2') and factors[3]==poly('2*beta-1')
 assert powers[:2]==[1,4]
 rad=poly(row['radical_other']);assert rad==factors[0]*factors[1];radicals.append(rad)
assert (A*radicals[0]+B*radicals[1]-s.Poly(D,b)).is_zero
print('Frozen forwardnorm1/reverse norm lineage, exact all-factor expansions, multiplicities, radicals67/85 and integer Bezout identity=nonzero scale: PASS',flush=True)
# Independently parse actual Horner syntax with univariate integer arrays.
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
 return s.Poly.from_dict({(m,):v for m,v in run(ast.parse(text,mode='eval').body).items()},b,domain=s.ZZ)
lines=src.splitlines()
for i,key in enumerate(['first_norm','second_norm']):
 line=next(l for l in lines if l.startswith(f'    (h{i} : '));expr=line.split(' : ',1)[1].rsplit(' = 0)',1)[0];assert (parse(expr)-poly(d[key])).is_zero
 for name,factor in [('f',rows[i]['factors'][0]['polynomial']),('g',rows[i]['factors'][1]['polynomial'])]:
  line=next(l for l in lines if l.startswith(f'  let {name}{i} : ℂ := '));assert (parse(line.split(' := ',1)[1])-poly(factor)).is_zero
 line=next(l for l in lines if l.startswith(f'  have hr{i} : '));assert (parse(line.split(' : ',1)[1].rsplit(' = 0 := by',1)[0])-radicals[i]).is_zero
line=next(l for l in lines if ' * hr0 + ' in l);pair=line.strip().removeprefix('linear_combination ').split(' * hr0 + ');assert len(pair)==2
assert parse(pair[0])==A and parse(pair[1].removesuffix(' * hr1'))==B
line=next(l for l in lines if l.startswith('  have impossible : '));assert int(re.search(r'\((\d+) : ℂ\)',line).group(1))==D
print('Actual Lean Horner hypotheses/factors/radicals/Bézout multipliers/constant parsed independently and matched coefficient-for-coefficient: PASS',flush=True)
assert len(src.splitlines())==49 and len(src.encode())==295027
assert len(re.findall(r'^theorem ',src,re.M))==1 and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',src)
assert all(l.endswith(' in') for l in lines if l.startswith('set_option '))
print('Scope: precisely the two explicit norm-zero hypotheses imply beta+2=0 or2beta-1=0. Removing endpoint powers uses case splits; g^4=0 implies g=0 in C. No original-equation necessity or whole-gap theorem asserted. Source review only; no compiler.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
