import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Basic.Complex.Basic

namespace PEqualNP.Outside.L_gct_231_aux

open Polynomial

lemma quartic_expansion_coeff_two_three
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) :
    p.coeff 2 = q ∧ p.coeff 3 = c := by
  rw [h]
  constructor <;> simp [coeff_add, coeff_C_mul_X_pow, coeff_C]

lemma quartic_coeffs_zero_of_eval_constant
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4)
    (heval : ∀ z : ℂ, p.eval z = 24) :
    q = 0 ∧ c = 0 := by
  have hp : p = C 24 := by
    apply Polynomial.funext
    intro z
    simpa only [eval_C] using heval z
  obtain ⟨h2, h3⟩ := quartic_expansion_coeff_two_three p q c r h
  constructor
  · rw [← h2, hp]
    simp [coeff_C]
  · rw [← h3, hp]
    simp [coeff_C]

lemma quartic_coeffs_zero_of_pointwise
    (q c r : ℂ)
    (h : ∀ z : ℂ, 24 + q * z ^ 2 + c * z ^ 3 + r * z ^ 4 = 24) :
    q = 0 ∧ c = 0 := by
  apply quartic_coeffs_zero_of_eval_constant
    (C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) q c r rfl
  intro z
  simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X] using h z

end PEqualNP.Outside.L_gct_231_aux
