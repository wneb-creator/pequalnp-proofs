import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.MixedMinorCoverage

def minor (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

lemma minor_zero_swap {u v : ℂ × ℂ} (h : minor u v = 0) : minor v u = 0 := by
  dsimp [minor] at h ⊢
  linear_combination -h

lemma minor_zero_of_common (u w v : ℂ × ℂ) (hv : v ≠ 0)
    (hu : minor u v = 0) (hw : minor w v = 0) : minor u w = 0 := by
  classical
  dsimp [minor] at hu hw ⊢
  by_cases hv₁ : v.1 = 0
  · have hv₂ : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext hv₁ h)
    have hz : v.2 * (u.1 * w.2 - u.2 * w.1) = 0 := by
      linear_combination w.2 * hu - u.2 * hw
    exact (mul_eq_zero.mp hz).resolve_left hv₂
  · have hz : v.1 * (u.1 * w.2 - u.2 * w.1) = 0 := by
      linear_combination w.1 * hu - u.1 * hw
    exact (mul_eq_zero.mp hz).resolve_left hv₁

theorem within_minors_zero (D O : Fin 3 → ℂ × ℂ)
    (hmixed : ∀ i j, minor (D i) (O j) = 0)
    (hD : ∃ i, D i ≠ 0) (hO : ∃ j, O j ≠ 0) :
    (∀ i j, minor (D i) (D j) = 0) ∧ (∀ i j, minor (O i) (O j) = 0) := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨o, ho⟩ := hO
  constructor
  · intro i j
    exact minor_zero_of_common (D i) (D j) (O o) ho (hmixed i o) (hmixed j o)
  · intro i j
    exact minor_zero_of_common (O i) (O j) (D d) hd
      (minor_zero_swap (hmixed d i)) (minor_zero_swap (hmixed d j))

end PEqualNP.Outside.L_gct_231_aux.MixedMinorCoverage
