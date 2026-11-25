from pathlib import Path
import json,sympy as S,hashlib
base=Path('/tmp/oec/pequalnp-pilot-75/gct231');out=base/'case2-necessity'
P,B,U,V,sat=S.symbols('P B U V sat');loc={str(x):x for x in(P,B,U,V,sat)}
d=json.loads((base/'c4-case2-resultants.json').read_text())
eq=[S.sympify(e,locals=loc) for e in d['source']['equations']]
rows={r['label']:S.sympify(r['polynomial'],locals=loc) for r in d['reductions']}
K=P**2+P-1;W=9*B**2-6*B*P**2-12*B+10*P**2
assert S.expand(eq[5]-(P*B*W*sat-1))==0
lean=lambda e:str(S.expand(e)).replace('**','^')
parts=['import Mathlib.RingTheory.Polynomial.Resultant.Basic\nimport Mathlib.Basic.Complex.Basic\nimport Mathlib.Tactic.LinearCombination\nimport Mathlib.Tactic.ComputeDegree\nimport Mathlib.Tactic.NormNum\n\nnamespace PEqualNP.Outside.L_gct_231_aux.Case2Necessity\n\nopen Polynomial\n']
for name,e in zip(['originalQ','originalC','scaleCurve','originalR','originalL'],eq[:5]):
 args='P B : ℂ' if name=='scaleCurve' else 'P B U V : ℂ'
 parts.append(f'\ndef {name} ({args}) : ℂ :=\n  {lean(e)}\n')
parts.append(f'\ndef chartDet (P B : ℂ) : ℂ :=\n  {lean(W)}\n\ndef curveLeading (P : ℂ) : ℂ := P^2 + P - 1\n')
rpoly=S.Poly(rows['linear_r'],U,V);lpoly=S.Poly(rows['quadratic_l'],U,V)
coefs={name:rpoly.coeff_monomial(mon) for name,mon in [('rA',U),('rB',V),('rC',1)]}
coefs.update({name:lpoly.coeff_monomial(mon) for name,mon in [('l20',U**2),('l11',U*V),('l10',U),('l02',V**2),('l01',V)]})
for name,e in coefs.items():parts.append(f'\ndef {name} (P B : ℂ) : ℂ :=\n  {lean(e)}\n')
certs={}
field=S.QQ.frac_field(P,U,V)
for idx,label in [(3,'linear_r'),(4,'quadratic_l')]:
 quo,rem=S.div(S.Poly(eq[idx],B,domain=field),S.Poly(eq[2],B,domain=field))
 num,den=S.fraction(S.cancel(rem.as_expr()));ratio=S.cancel(num/rows[label]);factor=S.factor(den/ratio);cofac=S.cancel(-den*quo.as_expr()/ratio)
 assert S.expand(rows[label]-factor*eq[idx]-cofac*eq[2])==0
 certs[label]={'factor':str(factor),'cofactor':str(cofac)}
 name='reduced_linear' if idx==3 else 'reduced_quadratic';orig='originalR' if idx==3 else 'originalL'
 target='rA P B * U + rB P B * V + rC P B' if idx==3 else 'l20 P B * U^2 + (l11 P B * V + l10 P B) * U + l02 P B * V^2 + l01 P B * V'
 defs='rA, rB, rC' if idx==3 else 'l20, l11, l10, l02, l01'
 parts.append(f'''\nset_option maxHeartbeats 800000 in
theorem {name} (P B U V : ℂ)
    (hF : scaleCurve P B = 0) (h : {orig} P B U V = 0) :
    {target} = 0 := by
  unfold scaleCurve {orig} at *
  unfold {defs.replace(',','')} 
  linear_combination ({lean(factor)}) * h + ({lean(cofac)}) * hF
''')
parts.append('''
theorem chart_nonzero (P B sat : ℂ)
    (hF : scaleCurve P B = 0)
    (hs : P * B * chartDet P B * sat - 1 = 0) :
    P ≠ 0 ∧ B ≠ 0 ∧ curveLeading P ≠ 0 ∧ chartDet P B ≠ 0 := by
  have hs' : P * B * chartDet P B * sat = 1 := sub_eq_zero.mp hs
  have hP : P ≠ 0 := by
    intro h
    simpa [h] using hs'
  have hB : B ≠ 0 := by
    intro h
    simpa [h] using hs'
  have hW : chartDet P B ≠ 0 := by
    intro h
    simpa [h] using hs'
  refine ⟨hP, hB, ?_, hW⟩
  intro hK
  have hpb : (3 : ℂ) * P * B = 0 := by
    unfold scaleCurve at hF
    unfold curveLeading at hK
    linear_combination -hF + (-6*B^2 + (5*P^2-P+10)*B - 8*P^2) * hK
  exact mul_ne_zero (mul_ne_zero (by norm_num) hP) hB hpb

theorem eliminate_quadratic (a t u A D E : ℂ)
    (hr : a*u+t=0) (hq : A*u^2+D*u+E=0) :
    A*t^2-a*D*t+a^2*E=0 := by
  linear_combination a^2*hq - (A*(a*u-t)+a*D)*hr

theorem eliminate_cubic (a t u A D E F : ℂ)
    (hr : a*u+t=0) (hc : A*u^3+D*u^2+E*u+F=0) :
    -A*t^3+a*D*t^2-a^2*E*t+a^3*F=0 := by
  linear_combination a^3*hc -
    (A*(a^2*u^2-a*u*t+t^2)+a*D*(a*u-t)+a^2*E)*hr

noncomputable def affinePolynomial (P B : ℂ) : Polynomial ℂ :=
  C (rB P B) * X + C (rC P B)

noncomputable def qEliminant (P B : ℂ) : Polynomial ℂ :=
  C (4*P^2-6*B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (4*P) * X) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (3*B-4) * X^2 + C (36*B))

noncomputable def lEliminant (P B : ℂ) : Polynomial ℂ :=
  C (l20 P B) * affinePolynomial P B ^ 2 -
  C (rA P B) * (C (l11 P B) * X + C (l10 P B)) * affinePolynomial P B +
  C (rA P B ^ 2) * (C (l02 P B) * X^2 + C (l01 P B) * X)

noncomputable def cEliminant (P B : ℂ) : Polynomial ℂ :=
  -C (2*P^2) * affinePolynomial P B ^ 3 +
  C (rA P B) * (C (-28*P^2) - C (4*P) * X) * affinePolynomial P B ^ 2 -
  C (rA P B ^ 2) * (-C (2*P) * X^2 + C (20*P) * X) * affinePolynomial P B +
  C (rA P B ^ 3) * (-X^3 + C (9*B-2) * X^2 - C (36*B))

theorem eliminant_degree_bounds (P B : ℂ) :
    (qEliminant P B).natDegree ≤ 2 ∧
    (lEliminant P B).natDegree ≤ 2 ∧
    (cEliminant P B).natDegree ≤ 3 := by
  unfold qEliminant lEliminant cEliminant affinePolynomial
  constructor
  · compute_degree
  constructor <;> compute_degree

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
theorem eliminants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    (qEliminant P B).eval V = 0 ∧
    (lEliminant P B).eval V = 0 ∧
    (cEliminant P B).eval V = 0 := by
  have hr' := reduced_linear P B U V hF hr
  have hl' := reduced_quadratic P B U V hF hl
  have hline : rA P B * U + (rB P B * V + rC P B) = 0 := by
    simpa [add_assoc] using hr'
  have hq' : (4*P^2-6*B)*U^2+(4*P*V)*U+((3*B-4)*V^2+36*B)=0 := by
    unfold originalQ at hq
    linear_combination hq
  have hc' : (2*P^2)*U^3+(-28*P^2-4*P*V)*U^2+
      (-2*P*V^2+20*P*V)*U+(-V^3+(9*B-2)*V^2-36*B)=0 := by
    unfold originalC at hc
    linear_combination hc
  have hqe := eliminate_quadratic (rA P B) (rB P B * V + rC P B) U _ _ _ hline hq'
  have hl'' : l20 P B * U^2 + (l11 P B * V + l10 P B) * U +
      (l02 P B * V^2 + l01 P B * V) = 0 := by
    simpa [add_assoc] using hl'
  have hle := eliminate_quadratic (rA P B) (rB P B * V + rC P B) U _ _ _ hline hl''
  have hce := eliminate_cubic (rA P B) (rB P B * V + rC P B) U _ _ _ _ hline hc'
  simp only [qEliminant, lEliminant, cEliminant, affinePolynomial,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · linear_combination hqe
  constructor
  · linear_combination hle
  · linear_combination hce

end PEqualNP.Outside.L_gct_231_aux.Case2Necessity
''')
source=''.join(parts)
(out/'Case2NecessaryElimination.lean').write_text(source)
(out/'reduction-certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
print(json.dumps({'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'bytes':len(source.encode()),'lines':len(source.splitlines())},indent=2))
