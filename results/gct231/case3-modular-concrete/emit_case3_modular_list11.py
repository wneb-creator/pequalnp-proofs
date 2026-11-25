from pathlib import Path
import sympy as S,json,hashlib
p=Path(__file__).parent;d=json.loads((p/'c4-case3-modular-coprime-p11.json').read_text());P=S.Symbol('P');api=(p/'PolynomialCoefficientList.lean').read_text()
def coeffs(key,typ):
 f=S.Poly(S.sympify(d[key],locals={'P':P}),P,domain=S.ZZ)
 return '(['+', '.join(str(int(c)) for c in reversed(f.all_coeffs()))+'] : List ('+typ+'))'
text='import PEqualNP.Defs\nimport Mathlib.Algebra.Field.ZMod\n'+api+'\nnamespace PEqualNP.Outside.L_gct_231.trace\nopen PEqualNP.Outside.L_gct_231_aux\n\n'
for name,key,typ in [('case3CofactorLeft','original_f','ℤ'),('case3CofactorRight','original_g','ℤ'),('case3ModLeft','mod_f','ZMod 11'),('case3ModRight','mod_g','ZMod 11')]:
 text+='noncomputable def '+name+' : Polynomial ('+typ+') := polynomialOfCoeffs '+coeffs(key,typ)+'\n\n'
text+='''set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_cofactor_degree_bounds :
    case3CofactorLeft.natDegree ≤ 67 ∧ case3CofactorRight.natDegree ≤ 85 := by
  constructor
  · unfold case3CofactorLeft
    exact polynomialOfCoeffs_degree_le _
  · unfold case3CofactorRight
    exact polynomialOfCoeffs_degree_le _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_left_map :
    case3CofactorLeft.map (Int.castRingHom (ZMod 11)) = case3ModLeft := by
  unfold case3CofactorLeft case3ModLeft
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_right_map :
    case3CofactorRight.map (Int.castRingHom (ZMod 11)) = case3ModRight := by
  unfold case3CofactorRight case3ModRight
  rw [polynomialOfCoeffs_map]
  congr 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case3_modular_degrees :
    (case3CofactorLeft.map (Int.castRingHom (ZMod 11))).natDegree = 67 ∧
    (case3CofactorRight.map (Int.castRingHom (ZMod 11))).natDegree = 85 := by
  rw [case3_left_map, case3_right_map]
  constructor
  · unfold case3ModLeft
    apply polynomialOfCoeffs_degree_eq _ 67 (by rfl)
    decide
  · unfold case3ModRight
    apply polynomialOfCoeffs_degree_eq _ 85 (by rfl)
    decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case3_modular_coprime :
    IsCoprime (case3CofactorLeft.map (Int.castRingHom (ZMod 11)))
      (case3CofactorRight.map (Int.castRingHom (ZMod 11))) := by
  rw [case3_left_map, case3_right_map]
  refine ⟨polynomialOfCoeffs '''+coeffs('mod_a','ZMod 11')+', polynomialOfCoeffs '+coeffs('mod_b','ZMod 11')+''', ?_⟩
  have hp : (11 : Polynomial (ZMod 11)) = 0 := by
    have h : (11 : ZMod 11) = 0 := by decide
    simpa only [map_ofNat, Polynomial.C_0] using congrArg (Polynomial.C : ZMod 11 → Polynomial (ZMod 11)) h
  have hh : polynomialOfCoeffs '''+coeffs('integer_quotient','ZMod 11')+''' * (11 : Polynomial (ZMod 11)) = 0 := by rw [hp, mul_zero]
  unfold case3ModLeft case3ModRight
  simp only [polynomialOfCoeffs, map_ofNat, Polynomial.C_0, Polynomial.C_1] at hh ⊢
  linear_combination hh

end PEqualNP.Outside.L_gct_231.trace
'''
out=p/'C4Case3ModularCoprimeList11.lean';out.write_text(text);print({'bytes':out.stat().st_size,'lines':len(text.splitlines()),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
