import Mathlib

namespace PEqualNP.Outside.L_gct_231

lemma crossedStar_no_extension (u v : ℂ)
    (hq : 4 * u ^ 2 - 12 * u * v - 63 * v ^ 2 = 0)
    (hc : v * (4 * u ^ 2 - 12 * u * v - 39 * v ^ 2) = 0) :
    u = 0 ∧ v = 0 := by
  have hv3 : v ^ 3 = 0 := by
    linear_combination (1 / 24 : ℂ) * hc - (v / 24) * hq
  have hv : v = 0 := eq_zero_of_pow_eq_zero hv3
  subst v
  have hu2 : u ^ 2 = 0 := by
    linear_combination (1 / 4 : ℂ) * hq
  exact ⟨eq_zero_of_pow_eq_zero hu2, rfl⟩

end PEqualNP.Outside.L_gct_231
