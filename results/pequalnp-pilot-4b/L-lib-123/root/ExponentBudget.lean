import Mathlib

namespace PEqualNP.Outside.ExponentBudget

open Filter

lemma poly_lt_two_pow (C d : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ C * n ^ d < 2 ^ n := by
  have ht : Tendsto (fun n : ℕ => (C : ℝ) * ((n : ℝ) ^ d / (2 : ℝ) ^ n))
      atTop (nhds 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt d
      (by norm_num : (1 : ℝ) < 2)).const_mul (C : ℝ)
  rcases ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).and
      (eventually_ge_atTop 1)).exists with ⟨n, hn, hpos⟩
  refine ⟨n, hpos, ?_⟩
  have hr : (C : ℝ) * (n : ℝ) ^ d < (2 : ℝ) ^ n := by
    apply (div_lt_one (by positivity : (0 : ℝ) < 2 ^ n)).mp
    simpa [mul_div_assoc] using hn
  exact_mod_cast hr

lemma polynomial_slack_cannot_cover_gap (p q K d : ℕ) (hpq : p < q) :
    ∃ n : ℕ, K * n ^ d * 2 ^ (p * n) + K < 2 ^ (q * n) := by
  obtain ⟨n, hn, hsmall⟩ := poly_lt_two_pow (2 * K + 1) d
  have hpoly : 1 ≤ n ^ d := one_le_pow₀ hn
  have hexp : 1 ≤ 2 ^ (p * n) := Nat.one_le_two_pow
  have hq : (p + 1) * n ≤ q * n := Nat.mul_le_mul_right n (by omega)
  have hlarge : 2 ^ ((p + 1) * n) ≤ 2 ^ (q * n) :=
    Nat.pow_le_pow_right (by decide) hq
  rw [Nat.add_mul, one_mul, pow_add] at hlarge
  have hscale := Nat.mul_lt_mul_of_pos_right hsmall
    (show 0 < 2 ^ (p * n) by positivity)
  have hk : K ≤ K * n ^ d * 2 ^ (p * n) := by
    calc
      K = K * 1 * 1 := by simp
      _ ≤ K * n ^ d * 2 ^ (p * n) := by gcongr
  refine ⟨n, ?_⟩
  nlinarith

end PEqualNP.Outside.ExponentBudget
