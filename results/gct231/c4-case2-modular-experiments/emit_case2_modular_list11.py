from pathlib import Path
import sympy as S,json,hashlib
p=Path(__file__).parent;d=json.loads((p/'c4-case2-modular-coprime-p11.json').read_text());P=S.Symbol('P');api=(p/'PolynomialCoefficientList.lean').read_text()
def coeffs(key,typ):
 f=S.Poly(S.sympify(d[key],locals={'P':P}),P,domain=S.ZZ)
 return '(['+', '.join(str(int(c)) for c in reversed(f.all_coeffs()))+'] : List ('+typ+'))'
text='import PEqualNP.Defs\nimport Mathlib.Algebra.Field.ZMod\n'+api+'\nnamespace PEqualNP.Outside.L_gct_231.trace\nopen PEqualNP.Outside.L_gct_231_aux\n\n'
for name,key,typ in [('case2CofactorLeft','original_f','ℤ'),('case2CofactorRight','original_g','ℤ'),('case2ModLeft','mod_f','ZMod 11'),('case2ModRight','mod_g','ZMod 11')]:
 text+='noncomputable def '+name+' : Polynomial ('+typ+') := polynomialOfCoeffs '+coeffs(key,typ)+'\n\n'
text+='''set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_cofactor_degree_bounds :
    case2CofactorLeft.natDegree ≤ 54 ∧ case2CofactorRight.natDegree ≤ 82 := by
  constructor
  · unfold case2CofactorLeft
    exact polynomialOfCoeffs_degree_le _
  · unfold case2CofactorRight
    exact polynomialOfCoeffs_degree_le _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_left_map :
    case2CofactorLeft.map (Int.castRingHom (ZMod 11)) = case2ModLeft := by
  unfold case2CofactorLeft case2ModLeft
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_right_map :
    case2CofactorRight.map (Int.castRingHom (ZMod 11)) = case2ModRight := by
  unfold case2CofactorRight case2ModRight
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_degrees :
    (case2CofactorLeft.map (Int.castRingHom (ZMod 11))).natDegree = 54 ∧
    (case2CofactorRight.map (Int.castRingHom (ZMod 11))).natDegree = 82 := by
  rw [case2_left_map, case2_right_map]
  constructor
  · unfold case2ModLeft
    apply polynomialOfCoeffs_degree_eq _ 54 (by rfl)
    decide
  · unfold case2ModRight
    apply polynomialOfCoeffs_degree_eq _ 82 (by rfl)
    decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_coprime :
    IsCoprime (case2CofactorLeft.map (Int.castRingHom (ZMod 11)))
      (case2CofactorRight.map (Int.castRingHom (ZMod 11))) := by
  rw [case2_left_map, case2_right_map]
  refine ⟨polynomialOfCoeffs '''+coeffs('mod_a','ZMod 11')+', polynomialOfCoeffs '+coeffs('mod_b','ZMod 11')+''', ?_⟩
  have hp : (11 : Polynomial (ZMod 11)) = 0 := by
    have h : (11 : ZMod 11) = 0 := by decide
    rw [← Polynomial.C_eq_natCast 11, h, Polynomial.C_0]
  have hh : polynomialOfCoeffs '''+coeffs('integer_quotient','ZMod 11')+''' * (11 : Polynomial (ZMod 11)) = 0 := by rw [hp, mul_zero]
  unfold case2ModLeft case2ModRight
  simp only [polynomialOfCoeffs, map_ofNat, Polynomial.C_0, Polynomial.C_1] at hh ⊢
  linear_combination hh

end PEqualNP.Outside.L_gct_231.trace
'''
out=p/'C4Case2ModularCoprimeList11.lean';out.write_text(text);print({'bytes':out.stat().st_size,'lines':len(text.splitlines()),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
