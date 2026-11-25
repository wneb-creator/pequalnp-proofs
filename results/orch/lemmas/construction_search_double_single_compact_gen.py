from pathlib import Path
import json,importlib.util,sys,sympy as s,hashlib,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
job=Path('/tmp/oec/pequalnp-pilot-79');branch=sys.argv[1];variant=sys.argv[2];assert branch in ['same','cross'] and variant in ['horner','quotient'];reduced=branch=='same';base=('double-single-reduced-macaulay-same-d6' if reduced else 'double-single-macaulay-cross-graded-d6');input_name=('double-single-reduced-same.msolve' if reduced else 'root-double-single-kernels-cross-0.msolve');cert=json.loads((job/(base+'-exact-certificate.json')).read_text());meta=json.loads((job/(base+'-metadata.json')).read_text());spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng);names,prime,polys=ng.parse_input(job/input_name);assert prime==0 and names==meta['variables'];groups=[{} for _ in polys];r=names.index('rr')
for coefficient,(index,multiplier) in zip(cert['coefficients'],meta['row_origins']):
 if not coefficient:continue
 if variant=='quotient':
  if index==len(polys)-1:continue
  multiplier=list(multiplier);coefficient*=2**(multiplier[r]//2);multiplier[r]%=2
 key=tuple(multiplier);groups[index][key]=groups[index].get(key,0)+coefficient
groups=[{m:v for m,v in q.items() if v} for q in groups]
def combine(op,terms):
 if not terms:return 'cz 0'
 if len(terms)==1:return terms[0]
 m=len(terms)//2;return op+' ('+combine(op,terms[:m])+') ('+combine(op,terms[m:])+')'
def render(p):
 if p.is_Integer:return 'cz ('+str(p)+')'
 if p.is_Symbol:return str(p)
 if p.is_Add:return combine('ca',list(map(render,p.args)))
 if p.is_Mul:return combine('cm',list(map(render,p.args)))
 if p.is_Pow:return 'cp ('+render(p.args[0])+') '+str(p.args[1])
 raise ValueError(type(p))
def expression(poly,variables):return sum(s.Integer(v)*s.prod(t**e for t,e in zip(variables,m)) for m,v in poly.items())
def leanpoly(poly,variables=names):
 symbols=s.symbols(' '.join(variables));return render(s.horner(expression(poly,symbols),*symbols[::-1]))
symbols=s.symbols(' '.join(names));identity=s.expand(sum(expression(q,symbols)*expression(p,symbols) for q,p in zip(groups,polys))-cert['denominator']);remainder=s.Poly(identity,symbols[r]).rem(s.Poly(symbols[r]**2-2,symbols[r])).as_expr().expand() if variant=='quotient' else identity;assert remainder==0
ns='PEqualNP.Outside.L_gct_231_aux.DoubleSingle'+branch.capitalize()+variant.capitalize()+'Certificate';lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','','namespace '+ns,'','def ca (x y : ℂ) : ℂ := x + y','def cm (x y : ℂ) : ℂ := x * y','def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n','def cz (z : ℤ) : ℂ := z',''];active=[i for i,g in enumerate(groups) if g]
for i in active:lines.extend(['def coeff'+str(i)+' ('+' '.join(names)+' : ℂ) : ℂ :=','  '+leanpoly(groups[i]),''])
lemma=('reduced_same_obstruction' if reduced else 'normalized_cross_obstruction');lines.extend(['set_option maxHeartbeats 100000000 in','set_option maxRecDepth 100000 in','lemma '+lemma+' ('+' '.join(names)+' : ℂ)'])
for i,poly in enumerate(polys):lines.append('    (e'+str(i)+' : '+leanpoly(poly)+' = (0 : ℂ))')
lines.extend(['    : False := by'])
if variant=='quotient':lines.extend(['  have hrr : rr^2=2 := by','    simp only [ca,cm,cp,cz] at e'+str(len(polys)-1),'    linear_combination e'+str(len(polys)-1)])
lines.extend(['  have impossible : cz ('+str(cert['denominator'])+') = 0 := by','    linear_combination (norm := skip) '+' + '.join('(coeff'+str(i)+' '+' '.join(names)+') * e'+str(i) for i in active),'    simp only ['+', '.join('coeff'+str(i) for i in active)+', ca, cm, cp, cz]'])
lines.extend(['    ring_nf','    simp only [hrr]','    ring'] if variant=='quotient' else ['    ring']);lines.extend(['  norm_num [cz] at impossible',''])
if reduced:
 original_names,_,original=ng.parse_input(job/'root-double-single-kernels-same-0.msolve');elimination=json.loads((job/'double-single-reduced-same-elimination.json').read_text());bynew={m['reduced']:m for m in elimination['mapping'] if m['reduced'] is not None};local=dict(zip(names,symbols))
 lines.extend(['set_option maxHeartbeats 100000000 in','set_option maxRecDepth 100000 in','lemma normalized_same_obstruction ('+' '.join(original_names)+' : ℂ)'])
 for i,poly in enumerate(original):lines.append('    (e'+str(i)+' : '+leanpoly(poly,original_names)+' = (0 : ℂ))')
 lines.extend(['    : False := by','  simp only [ca, cm, cp, cz] at *','  have hg : g = 2 * (rr + 1) * (1 + j) - a - 2 * c := by','    linear_combination -(rr + 1) * e5 - (a + 2 * c + g) * e19','  have hk : k = -2 * (rr - 1) * (1 + i) - b - 2 * d := by','    linear_combination (rr - 1) * e8 - (b + 2 * d + k) * e19','  subst g','  subst k','  apply reduced_same_obstruction '+' '.join(names)])
 for index,poly in enumerate(polys):
  if index==len(polys)-1:lines.append('  · exact e19');continue
  item=bynew[index];quotient=s.Poly(s.sympify(item['quotient'],locals=local),*symbols,domain=s.ZZ);q=leanpoly(dict(quotient.terms()));expr='e'+str(item['original'])+' - ('+q+') * e19';content=item['content']
  if content==1:lines.extend(['  · linear_combination (norm := skip) '+expr,'    simp only [ca, cm, cp, cz]','    ring'])
  else:lines.extend(['  · have hm : cz ('+str(content)+') * ('+leanpoly(poly)+') = 0 := by','      linear_combination (norm := skip) '+expr,'      simp only [ca, cm, cp, cz]','      ring','    have hc : cz ('+str(content)+') ≠ 0 := by norm_num [cz]','    exact (mul_eq_zero.mp hm).resolve_left hc'])
lines.extend(['','end '+ns,'']);out=job/('DoubleSingle'+branch.capitalize()+variant.capitalize()+'Certificate.lean');out.write_text('\n'.join(lines));data={'branch':branch,'variant':variant,'source':str(out),'bytes':out.stat().st_size,'lines':len(lines),'certificate_terms':sum(map(len,groups)),'active_equations':active,'exact_original_polynomial_identity_verified':True,'identity_modulo_rr_squared_minus_two':variant=='quotient','sha256':hashlib.sha256(out.read_bytes()).hexdigest()};(job/('double-single-'+branch+'-'+variant+'-metadata.json')).write_text(json.dumps(data,indent=2));print(json.dumps(data),flush=True)
