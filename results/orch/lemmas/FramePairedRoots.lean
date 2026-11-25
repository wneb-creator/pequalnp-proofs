import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.FramePairedRoots

theorem norm_roots (a s r : ℂ) (hr : r ^ 2 = 2)
    (ha : a ^ 2 + 8 * a * s + 8 * s ^ 2 = 0) :
    a = (-4 + 2 * r) * s ∨ a = (-4 - 2 * r) * s := by
  have hh : (a - (-4 + 2 * r) * s) * (a - (-4 - 2 * r) * s) = 0 := by
    linear_combination ha - 4 * s ^ 2 * hr
  exact (mul_eq_zero.mp hh).imp sub_eq_zero.mp sub_eq_zero.mp

theorem opposite_pairs (a b s t r : ℂ) (hr : r ^ 2 = 2)
    (ha : a ^ 2 + 8 * a * s + 8 * s ^ 2 = 0)
    (hb : b ^ 2 + 8 * b * t + 8 * t ^ 2 = 0) (hab : a * b = 8 * s * t) :
    (a = (-4 + 2 * r) * s ∧ b = (-4 - 2 * r) * t) ∨
    (a = (-4 - 2 * r) * s ∧ b = (-4 + 2 * r) * t) := by
  have hminus : 1 - r ≠ 0 := by
    intro h
    have he : r = 1 := by linear_combination -h
    rw [he] at hr
    norm_num at hr
  have hplus : 1 + r ≠ 0 := by
    intro h
    have he : r = -1 := by linear_combination h
    rw [he] at hr
    norm_num at hr
  rcases norm_roots a s r hr ha with ha | ha <;>
    rcases norm_roots b t r hr hb with hb | hb
  · have hh : (1 - r) * (s * t) = 0 := by
      rw [ha, hb] at hab
      linear_combination (1 / 16 : ℂ) * hab - (s * t / 4) * hr
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hminus) with hs | ht
    · right
      constructor
      · simpa [hs] using ha
      · exact hb
    · left
      constructor
      · exact ha
      · simpa [ht] using hb
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · have hh : (1 + r) * (s * t) = 0 := by
      rw [ha, hb] at hab
      linear_combination (1 / 16 : ℂ) * hab - (s * t / 4) * hr
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hplus) with hs | ht
    · left
      constructor
      · simpa [hs] using ha
      · exact hb
    · right
      constructor
      · exact ha
      · simpa [ht] using hb

end PEqualNP.Outside.L_gct_231_aux.FramePairedRoots
