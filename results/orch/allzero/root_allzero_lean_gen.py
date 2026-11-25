from pathlib import Path
import importlib.util,json
job=Path('/tmp/oec/pequalnp-pilot-79');cert=json.loads((job/'root-allzero-original-exact-certificate.json').read_text())
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,prime,polys=ng.parse_input(job/'fresh_top_allzero_0.msolve');assert prime==0
multipliers=[{tuple(e):c for e,c in p} for p in cert['multipliers']]
coeffs=sorted({abs(c) for p in multipliers for c in p.values()});lookup={c:i for i,c in enumerate(coeffs)}
def combine(op,terms):
 if not terms:return '(0 : ℂ)'
 if len(terms)==1:return terms[0]
 n=len(terms)//2;return op+' ('+combine(op,terms[:n])+') ('+combine(op,terms[n:])+')'
def polytext(poly,aliases=False):
 terms=[]
 for ex,c in sorted(poly.items()):
  c=int(c)
  num=('k'+str(lookup[abs(c)])) if aliases else '(cz ('+str(abs(c))+'))'
  if c<0:num='(-'+num+')'
  factors=[num]+[('cp '+v+' '+str(e)) if e>1 else v for v,e in zip(names,ex) if e]
  terms.append(combine('cm',factors))
 return combine('ca',terms)
ns='PEqualNP.Outside.L_gct_231_aux.TopAllZeroCertificate'
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','','namespace '+ns,'','def ca (x y : ℂ) : ℂ := x+y','def cm (x y : ℂ) : ℂ := x*y','def cp (x : ℂ) (n : ℕ) : ℂ := x^n','def cz (z : ℤ) : ℂ := z','']
for i,c in enumerate(coeffs):lines.append('def k'+str(i)+' : ℂ := cz ('+str(c)+')')
for i,p in enumerate(multipliers):lines += ['','def coeff'+str(i)+' ('+' '.join(names)+' : ℂ) : ℂ :=', '  '+polytext(p,True)]
lines += ['','set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','lemma obstruction ('+' '.join(names)+' : ℂ)']
for i,p in enumerate(polys):lines.append('    (e'+str(i)+' : '+polytext(p)+' = (0 : ℂ))')
lines += ['    : False := by','  simp only [ca, cm, cp, cz] at *','  have impossible : cz ('+str(cert['denominator'])+') = (0 : ℂ) := by','    linear_combination (norm := skip) '+' + '.join('(coeff'+str(i)+' '+' '.join(names)+') * e'+str(i) for i in range(len(polys))),'    simp only ['+', '.join(['coeff'+str(i) for i in range(len(polys))]+['k'+str(i) for i in range(len(coeffs))]+['ca','cm','cp','cz'])+']','    ring','  norm_num [cz] at impossible','','end '+ns,'']
p=job/'TopAllZeroCertificate.lean';p.write_text('\n'.join(lines));print(json.dumps({'source':str(p),'bytes':p.stat().st_size,'lines':len(lines),'coefficient_aliases':len(coeffs)}),flush=True)
