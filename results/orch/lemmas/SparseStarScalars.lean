import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.SparseStar

theorem equal_scalar_impossible (z : ℂ) (h4 : z ^ 4 = 6)
    (h2 : z ^ 2 + z - 4 = 0) : False := by
  have hl : -9 * z + 14 = 0 := by
    linear_combination h4 - (z ^ 2 - z + 5) * h2
  have hh : (2 : ℂ) = 0 := by
    linear_combination -81 * h2 - (9 * z + 23) * hl
  norm_num at hh

theorem twisted_scalar_impossible (m : ℂ) (h4 : m ^ 4 = 96)
    (h2 : m ^ 2 - 10 * m - 16 = 0) : False := by
  have hl : 3 * m + 4 = 0 := by
    linear_combination (1 / 440 : ℂ) * (h4 - (m ^ 2 + 10 * m + 116) * h2)
  have hh : (8 : ℂ) = 0 := by
    linear_combination -9 * h2 + (3 * m - 34) * hl
  norm_num at hh

end PEqualNP.Outside.L_gct_231_aux.SparseStar
