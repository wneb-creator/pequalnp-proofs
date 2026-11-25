import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.IsotropicThree

lemma minor_zero (a b c d e f : ℂ)
    (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 0)
    (h₂ : d ^ 2 + e ^ 2 + f ^ 2 = 0)
    (h₃ : a * d + b * e + c * f = 0) : a * e - b * d = 0 := by
  apply eq_zero_of_pow_eq_zero (n := 2)
  linear_combination (d ^ 2 + e ^ 2) * h₁ - c ^ 2 * h₂ +
    (2 * c * f - (a * d + b * e + c * f)) * h₃

end PEqualNP.Outside.L_gct_231_aux.IsotropicThree
