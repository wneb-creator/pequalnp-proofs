import importlib.util,sympy as s
from pathlib import Path
job=Path('/tmp/oec/pequalnp-pilot-79')
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
parsed=ng.parse_input(job/'centered-two-natural-rational.msolve')
print(type(parsed).__name__,flush=True)
print(str(parsed)[:180],flush=True)
names,prime,polys=parsed
assert prime==0

def combine(op,terms):
 if len(terms)==1:return terms[0]
 mid=len(terms)//2
 return op+' ('+combine(op,terms[:mid])+') ('+combine(op,terms[mid:])+')'

def leanpoly(poly):
 terms=[]
 for monom,coef in poly.items():
  assert coef.denominator==1
  factors=['('+str(coef.numerator)+' : ℂ)']+[('cp '+names[j]+' '+str(e) if e>1 else names[j]) for j,e in enumerate(monom) if e]
  terms.append(combine('cm',factors))
 return combine('ca',terms)
source='import Mathlib.Basic.Complex.Basic\n\nnamespace PEqualNP.Outside.L_gct_231_aux\n\ndef ca (x y : ℂ) : ℂ := x + y\ndef cm (x y : ℂ) : ℂ := x * y\ndef cp (x : ℂ) (n : ℕ) : ℂ := x ^ n\n\nset_option maxHeartbeats 10000000 in\nlemma centered_two_elaboration_probe ('+' '.join(names)+' : ℂ)\n'
for k,p in enumerate(polys):source+='    (e'+str(k)+' : '+leanpoly(p)+' = (0 : ℂ))\n'
source+='    : True := by\n  exact True.intro\n\nend PEqualNP.Outside.L_gct_231_aux\n'
(job/'CenteredTwoElabTyped.lean').write_text(source)
(job/'CenteredTwoElab.lean').write_text(source)
for suffix in ['.log','-run.json']:
 p=job/('centered-two-direct-elab'+suffix)
 if p.exists():p.rename(job/('centered-two-direct-elab-coefficient-annotation-true'+suffix))
print('wrote',len(source),'characters',flush=True)
