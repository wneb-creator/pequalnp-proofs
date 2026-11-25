import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

theorem block_scalar_rigidity
    (a b p q : ℂ)
    (h1 : a + b = 0)
    (h2 : p + q + a * b = 0)
    (h3 : a * q + b * p = 0)
    (h4 : p * q = 0) :
    a = 0 ∧ b = 0 ∧ p = 0 ∧ q = 0 := by
  have ha3 : a ^ 3 = 0 := by
    rcases mul_eq_zero.mp h4 with hp | hq
    · linear_combination (a - b) * hp + a ^ 2 * h1 - a * h2 + h3
    · linear_combination (p + a ^ 2) * h1 - a * h2 - h3 + 2 * a * hq
  have ha : a = 0 := by
    have hm : a * (a * a) = 0 := by linear_combination ha3
    rcases mul_eq_zero.mp hm with ha | haa
    · exact ha
    · exact (mul_eq_zero.mp haa).elim id id
  have hb : b = 0 := by simpa [ha] using h1
  have hpq : p + q = 0 := by simpa [ha, hb] using h2
  rcases mul_eq_zero.mp h4 with hp | hq
  · exact ⟨ha, hb, hp, by simpa [hp] using hpq⟩
  · exact ⟨ha, hb, by simpa [hq] using hpq, hq⟩

end PEqualNP.Outside.L_gct_231_aux
