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

def pairedPermanent (b p c a r d : ℂ) : ℂ :=
  2 * b ^ 2 * (a * d + r ^ 2) + 4 * b * (a * c ^ 2 + d * p ^ 2 + 2 * p * c * r) +
    4 * p ^ 2 * c ^ 2

def pairedPlane (p c a d k b t : ℂ) : ℂ :=
  pairedPermanent b (p + (1 - p) * b) (c + (1 - c) * b)
    (a + (1 - a) * b + (k - 1) * t) (b + t)
    (d + (1 - d) * b - (1 + k) * t)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem paired_plane_impossible (p c a d k : ℂ)
    (h : ∀ b t : ℂ, pairedPlane p c a d k b t = 24) : False := by
  have h00 := h 0 0
  have h10 := h 1 0
  have hn10 := h (-1) 0
  have h20 := h 2 0
  have hn20 := h (-2) 0
  have h30 := h 3 0
  have h11 := h 1 1
  have h1n1 := h 1 (-1)
  have hn11 := h (-1) 1
  have hn1n1 := h (-1) (-1)
  have h21 := h 2 1
  have h2n1 := h 2 (-1)
  have hn21 := h (-2) 1
  have hn2n1 := h (-2) (-1)
  have hh1 := h (1 / 2) 1
  have hhn1 := h (1 / 2) (-1)
  simp only [pairedPlane, pairedPermanent] at h00 h10 hn10 h20 hn20 h30 h11 h1n1 hn11 hn1n1 h21 h2n1 hn21 hn2n1 hh1 hhn1
  have hk : k ^ 2 = 2 := by
    linear_combination (-1 / 4 : ℂ) * (h11 + h1n1 - 2 * h10)
  have hH : (p * c) ^ 2 = 6 := by
    linear_combination (1 / 4 : ℂ) * h00
  have hS : a + d = 16 - 4 * (p + c) := by
    linear_combination (-1 / 72 : ℂ) * hn10 + (1 / 9 : ℂ) * h00 -
      (1 / 9 : ℂ) * h20 + (1 / 72 : ℂ) * h30
  have hN : (c - p) * (k * (p + c) - (c - p)) = 0 := by
    linear_combination (1 / 12 : ℂ) * (h11 - h1n1 - hn11 + hn1n1) -
      (1 / 96 : ℂ) * (h21 - h2n1 - hn21 + hn2n1)
  have hD : k * (d - a) = a + d - 4 * k * (c - p) := by
    linear_combination 2 * (hh1 - hhn1) - 2 * hN
  have hE : a * c ^ 2 + d * p ^ 2 + 2 * (p * c) * (p + c - 2 * (p * c)) = 0 := by
    linear_combination (1 / 6 : ℂ) * (h10 - hn10) - (1 / 48 : ℂ) * (h20 - hn20)
  exact sparse_scalar_obstruction p c a d k hk hH hS hD hN hE

end PEqualNP.Outside.L_gct_231_aux.SparseStar
