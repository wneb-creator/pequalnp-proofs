import Mathlib

namespace PEqualNP.Outside.L_lib_123_Audit

open Filter Topology

lemma block_height_product_bound (T b h : ℝ) (hT : T ≤ b * h) :
    4 * T ≤ (b + h) ^ 2 := by
  nlinarith [sq_nonneg (b - h)]

lemma no_polynomial_block_budget (C : ℕ) :
    ∃ m : ℕ, ¬ ∃ b h : ℝ, 0 ≤ b ∧ 0 ≤ h ∧
      (2 : ℝ) ^ m ≤ b * h ∧ b + h ≤ (C : ℝ) * m := by
  have hlim :=
    (tendsto_pow_const_div_const_pow_of_one_lt 2 (show 1 < (2 : ℝ) by norm_num)).const_mul
      ((C : ℝ) ^ 2)
  have hevent : ∀ᶠ m : ℕ in atTop,
      (C : ℝ) ^ 2 * ((m : ℝ) ^ 2 / (2 : ℝ) ^ m) < 4 := by
    exact hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨m, hm⟩ := hevent.exists
  refine ⟨m, ?_⟩
  rintro ⟨b, h, hb, hh, hT, hsum⟩
  have hp : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hexp : (C : ℝ) ^ 2 * (m : ℝ) ^ 2 < 4 * (2 : ℝ) ^ m := by
    apply (div_lt_iff₀ hp).mp
    simpa only [mul_div_assoc] using hm
  have hsquare : (b + h) ^ 2 ≤ ((C : ℝ) * m) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsum 2
  have hproduct := block_height_product_bound ((2 : ℝ) ^ m) b h hT
  nlinarith

lemma le_power_two (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < (2 : ℕ) ^ n := by positivity
    rw [pow_succ]
    omega

lemma tree_cut_budget (T b H d : ℕ) (hT : T ≤ b * H) (hd : d ≤ H) :
    T ≤ b * (2 ^ d + 2 ^ (H - d)) := by
  apply hT.trans
  apply Nat.mul_le_mul_left
  have h1 := le_power_two d
  have h2 := le_power_two (H - d)
  omega

end PEqualNP.Outside.L_lib_123_Audit
