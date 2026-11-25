import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

theorem case3_beta_neg2_A_three32_impossible (U V : ℂ)
    (hq : -135 * U ^ 2 + 96 * U * V + 1024 * V ^ 2 + 864 = 0)
    (hr : -45 * U + 16 * V - 258 = 0)
    (hl : V * (45 * U - 16 * V + 348) = 0) : False := by
  have hV : V = 0 := by
    linear_combination (1 / 90 : ℂ) * hl + (V / 90) * hr
  have hU : U = -86 / 15 := by
    linear_combination (-1 / 45 : ℂ) * hr + (16 / 45 : ℂ) * hV
  rw [hU, hV] at hq
  norm_num at hq

theorem case3_beta_half_A_four_unique (U V : ℂ)
    (hq : 40 * U ^ 2 + 16 * U * V - V ^ 2 + 144 = 0)
    (hc : 64 * U ^ 3 - 32 * U ^ 2 * V - 896 * U ^ 2 +
      3 * U * V ^ 2 + 160 * U * V + 2 * V ^ 2 - 288 = 0)
    (hr : 5 * U + V + 12 = 0) : U = 0 ∧ V = -12 := by
  have hV : V = -5 * U - 12 := by linear_combination hr
  rw [hV] at hq hc
  have hf : U * (5 * U + 24) = 0 := by
    linear_combination (-1 / 13 : ℂ) * hq
  have hg : U * (299 * U ^ 2 - 902 * U - 1248) = 0 := by
    linear_combination hc
  have hU : U = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · exact h
    · have he : U = -24 / 5 := by linear_combination (1 / 5 : ℂ) * h
      rw [he] at hg
      norm_num at hg
  constructor
  · exact hU
  · rw [hU] at hV
    norm_num at hV
    exact hV

end PEqualNP.Outside.L_gct_231_aux
