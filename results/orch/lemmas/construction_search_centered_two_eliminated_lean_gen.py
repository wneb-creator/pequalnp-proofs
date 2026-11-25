from pathlib import Path
import importlib.util
p=Path('/tmp/oec/pequalnp-pilot-79');spec=importlib.util.spec_from_file_location('ng',p/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,prime,polys=ng.parse_input(p/'centered-two-eliminated-rational.msolve');assert prime==0

def combine(op,terms):
 if len(terms)==1:return terms[0]
 mid=len(terms)//2;return op+' ('+combine(op,terms[:mid])+') ('+combine(op,terms[mid:])+')'
def leanpoly(poly):
 terms=[]
 for monom,coef in poly.items():
  assert coef.denominator==1
  factors=['('+str(coef.numerator)+' : ℂ)']+[('cp '+names[j]+' '+str(e) if e>1 else names[j]) for j,e in enumerate(monom) if e]
  terms.append(combine('cm',factors))
 return combine('ca',terms)
src='import Mathlib.Basic.Complex.Basic\n\nnamespace PEqualNP.Outside.L_gct_231_aux\n\ndef ca (x y : ℂ) : ℂ := x + y\ndef cm (x y : ℂ) : ℂ := x * y\ndef cp (x : ℂ) (n : ℕ) : ℂ := x ^ n\n\nset_option maxHeartbeats 10000000 in\nset_option maxRecDepth 100000 in\nlemma centered_two_eliminated_chart_obstruction ('+' '.join(names)+' : ℂ)\n'
for j,poly in enumerate(polys):src+='    (e'+str(j)+' : '+leanpoly(poly)+' = (0 : ℂ))\n'
src+='    : False := by\n  simp only [ca, cm, cp] at *\n  grind (ringSteps := 5000000) only\n\nend PEqualNP.Outside.L_gct_231_aux\n'
(p/'CenteredTwoChartEliminated.lean').write_text(src)
(p/'CenteredTwoChartNatural.lean').write_text((p/'CenteredTwoChart.lean').read_text());(p/'CenteredTwoChart.lean').write_text(src)
for suffix in ['.log','-run.json']:
 f=p/('centered-two-direct-complex'+suffix);f.rename(p/('centered-two-direct-complex-100000000steps'+suffix))
print('bytes',len(src),flush=True)
