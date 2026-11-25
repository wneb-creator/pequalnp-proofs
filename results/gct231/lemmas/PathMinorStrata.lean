import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

theorem path_minor_strata
    (a b c d e f g h j : ℂ)
    (h0 : b * f - c * e = 0)
    (h1 : j = 0)
    (h2 : a = 0)
    (h3 : d * h - e * g = 0)
    (h4 : -c = 0)
    (h5 : e * j - f * h = 0)
    (h6 : a * e - b * d = 0)
    (h7 : -g = 0) :
    a = 0 ∧ c = 0 ∧ g = 0 ∧ j = 0 ∧
      ((d = 0 ∧ f = 0) ∨ (b = 0 ∧ h = 0)) := by
  have hc : c = 0 := neg_eq_zero.mp h4
  have hg : g = 0 := neg_eq_zero.mp h7
  have hbf : b * f = 0 := by simpa [hc] using h0
  have hdh : d * h = 0 := by simpa [hg] using h3
  have hfh : f * h = 0 := by linear_combination e * h1 - h5
  have hbd : b * d = 0 := by linear_combination e * h2 - h6
  refine ⟨h2, hc, hg, h1, ?_⟩
  by_cases hd : d = 0
  · by_cases hf : f = 0
    · exact Or.inl ⟨hd, hf⟩
    · exact Or.inr ⟨(mul_eq_zero.mp hbf).resolve_right hf,
        (mul_eq_zero.mp hfh).resolve_left hf⟩
  · exact Or.inr ⟨(mul_eq_zero.mp hbd).resolve_right hd,
      (mul_eq_zero.mp hdh).resolve_left hd⟩

end PEqualNP.Outside.L_gct_231_aux
