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

theorem sparse_scalar_obstruction (p c a d k : ℂ)
    (hk : k ^ 2 = 2) (hH : (p * c) ^ 2 = 6)
    (hS : a + d = 16 - 4 * (p + c))
    (hD : k * (d - a) = a + d - 4 * k * (c - p))
    (hN : (c - p) * (k * (p + c) - (c - p)) = 0)
    (hE : a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (p + c - 2 * (p * c)) = 0) :
    False := by
  rcases mul_eq_zero.mp hN with hN | hN
  · have hcp : c = p := sub_eq_zero.mp hN
    subst c
    have h4 : p ^ 4 = 6 := by linear_combination hH
    have hp : p ≠ 0 := by
      intro hp
      subst p
      norm_num at h4
    have hq : p ^ 2 * (p ^ 2 + p - 4) = 0 := by
      linear_combination (-1 / 4 : ℂ) * hE + (p ^ 2 / 4) * hS
    exact equal_scalar_impossible p h4 ((mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hp))
  · have hN : c - p = k * (p + c) := (sub_eq_zero.mp hN).symm
    let m := p + c
    have hp : p = (1 - k) * m / 2 := by
      dsimp [m]
      linear_combination (-1 / 2 : ℂ) * hN
    have hc : c = (1 + k) * m / 2 := by
      dsimp [m]
      linear_combination (1 / 2 : ℂ) * hN
    have ha : a = 8 - 2 * m - 4 * k + 3 * k * m := by
      dsimp [m]
      linear_combination (-k / 4) * hD + ((d - a) / 4 + (c - p)) * hk +
        (1 / 2 - k / 4) * hS + 2 * hN
    have hd : d = 8 - 2 * m + 4 * k - 3 * k * m := by
      dsimp [m] at ha ⊢
      linear_combination hS - ha
    have h4 : m ^ 4 = 96 := by
      rw [hp, hc] at hH
      linear_combination 16 * hH - (k ^ 2 * m ^ 4) * hk
    have hm : m ≠ 0 := by
      intro hm
      rw [hm] at h4
      norm_num at h4
    have hq : m ^ 2 * (m ^ 2 - 10 * m - 16) = 0 := by
      change a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (m - 2 * (p * c)) = 0 at hE
      rw [hp, hc, ha, hd] at hE
      linear_combination -4 * hE + (-k ^ 2 * m ^ 4 + 6 * m ^ 3) * hk
    exact twisted_scalar_impossible m h4
      ((mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hm))

end PEqualNP.Outside.L_gct_231_aux.SparseStar
