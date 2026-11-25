from pathlib import Path
import json,importlib.util,sys
job=Path('/tmp/oec/pequalnp-pilot-79');chart=int(sys.argv[1]);assert chart in [2,3];base='centered-two-macaulay-'+str(chart)+'-d9'
cert=json.loads((job/(base+'-exact-certificate.json')).read_text());meta=json.loads((job/(base+'-metadata.json')).read_text());spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng);names,prime,polys=ng.parse_input(job/('centered-two-coordinate-'+str(chart)+'-rational.msolve'));assert prime==0 and names==meta['variables']
groups=[{} for _ in polys]
for coefficient,(index,multiplier) in zip(cert['coefficients'],meta['row_origins']):
 if coefficient:groups[index][tuple(multiplier)]=coefficient

def combine(op,terms):
 if not terms:return '(0 : ℂ)'
 if len(terms)==1:return terms[0]
 mid=len(terms)//2;return op+' ('+combine(op,terms[:mid])+') ('+combine(op,terms[mid:])+')'
def leanpoly(poly):
 terms=[]
 for monomial,coefficient in poly.items():
  assert int(coefficient)==coefficient
  factors=['('+str(int(coefficient))+' : ℂ)']+[('cp '+names[j]+' '+str(e) if e>1 else names[j]) for j,e in enumerate(monomial) if e]
  terms.append(combine('cm',factors))
 return combine('ca',terms)
ns='PEqualNP.Outside.L_gct_231_aux.CenteredTwoCertificate'+str(chart)
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','','namespace '+ns,'','def ca (x y : ℂ) : ℂ := x + y','def cm (x y : ℂ) : ℂ := x * y','def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n','']
active=[i for i,g in enumerate(groups) if g]
for i in active:
 lines.extend(['def coeff'+str(i)+' ('+' '.join(names)+' : ℂ) : ℂ :=', '  '+leanpoly(groups[i]),''])
lines.extend(['set_option maxHeartbeats 100000000 in','set_option maxRecDepth 100000 in','lemma mixed_chart'+str(chart)+'_obstruction ('+' '.join(names)+' : ℂ)'])
for i in active:lines.append('    (e'+str(i)+' : '+leanpoly(polys[i])+' = (0 : ℂ))')
lines.extend(['    : False := by','  have impossible : ('+str(cert['denominator'])+' : ℂ) = 0 := by','    linear_combination (norm := skip) '+' + '.join('(coeff'+str(i)+' '+' '.join(names)+') * e'+str(i) for i in active),'    simp only ['+', '.join('coeff'+str(i) for i in active)+', ca, cm, cp]','    ring','  norm_num at impossible','','end '+ns,''])
output=job/('CenteredTwoCertificate'+str(chart)+'.lean');output.write_text('\n'.join(lines));print(json.dumps({'chart':chart,'bytes':output.stat().st_size,'lines':len(lines),'active_equations':active,'classification':'Explicit standalone Lean certificate trial, not yet compiled; research source exceeds final PR limit'}),flush=True)
