from pathlib import Path
from fractions import Fraction
import hashlib,json,math

out=Path(__file__).parent
data=json.loads((out/'star-r-flat-certificate.json').read_text())
names=data['variables'];D=1
for terms in data['multipliers']:
 for mon,c in terms:D=math.lcm(D,Fraction(c).denominator)
def balanced(terms):
 if not terms:return '0'
 if len(terms)==1:return terms[0]
 k=len(terms)//2
 return '('+balanced(terms[:k])+' + '+balanced(terms[k:])+')'
def polynomial(terms,scale=1):
 pieces=[]
 for mon,c in terms:
  coefficient=Fraction(c)*scale;assert coefficient.denominator==1
  coefficient=int(coefficient)
  factors=[v if e==1 else v+' ^ '+str(e) for v,e in zip(names,mon) if e]
  m=' * '.join(factors)
  if not m:piece=str(coefficient)
  elif coefficient==1:piece=m
  elif coefficient==-1:piece='-('+m+')'
  else:piece=str(coefficient)+' * '+m
  pieces.append('('+piece+')')
 return balanced(pieces)
indices=[i for i,terms in enumerate(data['multipliers']) if terms]
hypotheses=['    (h'+str(i)+' : ('+polynomial(data['generators'][i])+' : ℂ) = 0)' for i in indices]
namespace='PEqualNP.Outside.L_gct_231_aux.StarPencil'
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','import Mathlib.Tactic.NormNum','',
       'namespace '+namespace,'','set_option maxRecDepth 4096 in','set_option maxHeartbeats 4000000 in',
       'theorem r_eq_zero_of_coefficients (p q r a b : ℂ)']+hypotheses+[
       '    : r = 0 := by',
       '  have hr : ('+str(D)+' : ℂ) * r = 0 := by',
       '    linear_combination '+balanced(['('+polynomial(data['multipliers'][i],D)+') * h'+str(i) for i in indices]),
       '  exact (mul_eq_zero.mp hr).resolve_left (by norm_num)','',
       'theorem coefficients_force_standard_star (p q r a b : ℂ)']+hypotheses+[
       '    : p = 0 ∧ q = 0 ∧ r = 0 ∧ a = -1 ∧ b = -1 := by',
       '  have hr := r_eq_zero_of_coefficients p q r a b '+' '.join('h'+str(i) for i in indices),
       '  have hp : p = 0 := by simpa [hr] using h6',
       '  have hq : q = 0 := by simpa [hr] using h7',
       '  have ha2 : (a + 1) ^ 2 = 0 := by',
       '    have hh := h2',
       '    simp only [hp, hr, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, neg_zero] at hh',
       '    linear_combination hh',
       '  have hb2 : (b + 1) ^ 2 = 0 := by',
       '    have hh := h5',
       '    simp only [hq, hr, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, neg_zero] at hh',
       '    linear_combination hh',
       '  have ha1 : a + 1 = 0 := by',
       '    have hh : (a + 1) * (a + 1) = 0 := by simpa only [pow_two] using ha2',
       '    exact (mul_eq_zero.mp hh).elim id id',
       '  have hb1 : b + 1 = 0 := by',
       '    have hh : (b + 1) * (b + 1) = 0 := by simpa only [pow_two] using hb2',
       '    exact (mul_eq_zero.mp hh).elim id id',
       '  refine ⟨hp, hq, hr, ?_, ?_⟩',
       '  · linear_combination ha1',
       '  · linear_combination hb1','',
       'end '+namespace,'']
path=out/'StarPencilClassification.lean';path.write_text('\n'.join(lines))
print('lean_bytes',path.stat().st_size,'lines',len(lines),'sha256',hashlib.sha256(path.read_bytes()).hexdigest(),'common_denominator',D)
