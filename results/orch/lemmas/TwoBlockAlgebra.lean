import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231.TwoBlock

lemma branch_zero (h t x y : ℂ)
    (hh : h ^ 2 = 2)
    (hy : y * (2*h*x+t+3*y) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-6*y^2 = 0)
    (hc : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+t^2*x+2*t*x*y-4*x*y^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 := by
  by_cases hy0 : y = 0
  · subst y
    have hx3 : x ^ 3 = 0 := by
      linear_combination (x/4)*hq + (3/4 : ℂ)*hc
    have hx : x = 0 := eq_zero_of_pow_eq_zero hx3
    subst x
    have ht2 : t ^ 2 = 0 := by linear_combination (-1/3 : ℂ)*hq
    exact ⟨eq_zero_of_pow_eq_zero ht2, rfl, rfl⟩
  · have hl : 2*h*x+t+3*y = 0 := (mul_eq_zero.mp hy).resolve_left hy0
    have ht : t = -2*h*x-3*y := by linear_combination hl
    rw [ht] at hq hc
    have hQ : -20*x^2-12*h*x*y+3*y^2 = 0 := by
      linear_combination hq + 12*x^2*hh
    have hRprod : x * (8*x^2+4*h*x*y-5*y^2) = 0 := by
      linear_combination hc - 2*x*(-2*h*x*y+2*x^2-y^2)*hh
    by_cases hx0 : x = 0
    · have hy2 : y ^ 2 = 0 := by
        subst x
        linear_combination (1/3 : ℂ)*hQ
      exact False.elim (hy0 (eq_zero_of_pow_eq_zero hy2))
    · have hR : 8*x^2+4*h*x*y-5*y^2 = 0 :=
        (mul_eq_zero.mp hRprod).resolve_left hx0
      have hxl : x * (19*x+12*h*y) = 0 := by
        linear_combination (-5/4 : ℂ)*hQ - (3/4 : ℂ)*hR
      have hL : 19*x+12*h*y = 0 := (mul_eq_zero.mp hxl).resolve_left hx0
      have hx2 : x ^ 2 = 0 := by
        linear_combination ((115*x-12*h*y)/265)*hL +
          (144*y^2/265)*hh + (96/265 : ℂ)*hQ
      exact False.elim (hx0 (eq_zero_of_pow_eq_zero hx2))

lemma quadrics_and_cubic_zero (h t x y z : ℂ)
    (hh : h ^ 2 = 2)
    (h0 : (y-z)*(y+z) = 0)
    (h1 : (y+z)*(4*h*x+2*t+5*y+z) = 0)
    (h2 : (y-z)*(4*h*x-2*t-5*y+z) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-9*y^2+3*z^2 = 0)
    (hc : -h*t^2*z-5*h*t*y*z+4*h*x^2*z-6*h*y^2*z+
      t^2*x+2*t*x*y-2*x*y^2-2*x*z^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  rcases mul_eq_zero.mp h0 with hm | hp
  · have hz : z = y := (sub_eq_zero.mp hm).symm
    subst z
    have hy : y*(2*h*x+t+3*y) = 0 := by linear_combination (1/4 : ℂ)*h1
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero h t x y hh hy hq' hc' with ⟨ht, hx, hy0⟩
    exact ⟨ht, hx, hy0, hy0⟩
  · have hz : z = -y := by linear_combination hp
    rw [hz] at h2 hq hc
    have hh' : (-h)^2 = 2 := by linear_combination hh
    have hy : y*(2*(-h)*x+t+3*y) = 0 := by linear_combination (-1/4 : ℂ)*h2
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -(-h)*t^2*y-5*(-h)*t*y^2+4*(-h)*x^2*y-6*(-h)*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero (-h) t x y hh' hy hq' hc' with ⟨ht, hx, hy0⟩
    refine ⟨ht, hx, hy0, ?_⟩
    simpa only [hy0, neg_zero] using hz

end PEqualNP.Outside.L_gct_231.TwoBlock
