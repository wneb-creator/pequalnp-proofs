import Mathlib

namespace PriorRoutes

open Filter

lemma choose_integer_exponents (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ α * (q : ℝ) < (p : ℝ) := by
  have hd : 0 < 1 - α := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / (1 - α))
  have hm : 2 < (q : ℝ) * (1 - α) := (div_lt_iff₀ hd).mp hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hq2 : (2 : ℝ) < q := by nlinarith
  have hq2n : 2 < q := by exact_mod_cast hq2
  refine ⟨q - 1, q, by omega, by omega, ?_⟩
  have hc : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hc]
  nlinarith

lemma poly_exp_eventual (a b : ℝ) (k : ℕ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k * a ^ n ≤ b ^ n := by
  have hsmall := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) k (r₁ := a) (r₂ := b) (by simpa [Real.norm_eq_abs, abs_of_nonneg ha])
  filter_upwards [hsmall.eventuallyLE] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (pow_nonneg (Nat.cast_nonneg n) k) (pow_nonneg ha n)),
    abs_of_nonneg (pow_nonneg (le_trans ha hab.le) n)] using hn

lemma eventual_to_global_exp_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (b : ℝ) (hb : 1 ≤ b) (hev : ∀ᶠ n : ℕ in atTop, f n ≤ b ^ n) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ, f n ≤ (K : ℝ) * b ^ n := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  let A : ℝ := 1 + ∑ i ∈ Finset.range n₀, f i
  have hsum : 0 ≤ ∑ i ∈ Finset.range n₀, f i := by
    exact Finset.sum_nonneg (fun i _ => hf i)
  obtain ⟨K, hK⟩ := exists_nat_gt A
  have hK1 : (1 : ℝ) ≤ K := by dsimp [A] at hK; linarith
  refine ⟨K, by exact_mod_cast hK1, ?_⟩
  intro n
  have hpow : 1 ≤ b ^ n := one_le_pow₀ hb
  by_cases hn : n₀ ≤ n
  · have hn' := hn₀ n hn
    nlinarith
  · have hmem : n ∈ Finset.range n₀ := Finset.mem_range.mpr (by omega)
    have hsingle : f n ≤ ∑ i ∈ Finset.range n₀, f i :=
      Finset.single_le_sum (fun i _ => hf i) hmem
    dsimp [A] at hK
    have hfn : f n ≤ (K : ℝ) := by linarith
    nlinarith

lemma poly_exp_global (a b : ℝ) (k : ℕ) (ha : 0 ≤ a) (hb : 1 ≤ b) (hab : a < b) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ,
      (n : ℝ) ^ k * a ^ n ≤ (K : ℝ) * b ^ n := by
  apply eventual_to_global_exp_bound _ (fun n =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) (pow_nonneg ha n)) b hb
  exact poly_exp_eventual a b k ha hab

lemma poly_exp_global_shifted (a b : ℝ) (k C : ℕ)
    (ha : 0 ≤ a) (hb : 1 ≤ b) (hab : a < b) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ,
      (C : ℝ) * ((n : ℝ) + 1) ^ k * a ^ n ≤ (K : ℝ) * b ^ n := by
  obtain ⟨K₀, hK₀, hbound⟩ := poly_exp_global a b k ha hb hab
  let K := C * (2 ^ k * K₀ + 1) + 1
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro n
  have hcoeff : (C : ℝ) * 2 ^ k * K₀ ≤ (K : ℝ) := by
    dsimp [K]
    push_cast
    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one]
    have hnat : C ≤ K := by
      dsimp [K]
      nlinarith [Nat.zero_le (2 ^ k * K₀)]
    exact_mod_cast hnat
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hp : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
      calc
        ((n : ℝ) + 1) ^ k ≤ (2 * (n : ℝ)) ^ k := by gcongr; linarith
        _ = 2 ^ k * (n : ℝ) ^ k := mul_pow _ _ _
    calc
      (C : ℝ) * ((n : ℝ) + 1) ^ k * a ^ n
          ≤ (C : ℝ) * (2 ^ k * (n : ℝ) ^ k) * a ^ n := by
            gcongr
      _ = ((C : ℝ) * 2 ^ k) * ((n : ℝ) ^ k * a ^ n) := by ring
      _ ≤ ((C : ℝ) * 2 ^ k) * ((K₀ : ℝ) * b ^ n) := by
            exact mul_le_mul_of_nonneg_left (hbound n)
              (mul_nonneg (Nat.cast_nonneg C) (by positivity))
      _ = ((C : ℝ) * 2 ^ k * K₀) * b ^ n := by ring
      _ ≤ (K : ℝ) * b ^ n := mul_le_mul_of_nonneg_right hcoeff
        (pow_nonneg (by linarith : 0 ≤ b) _)

lemma circuit_exponent_budget (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ ∀ C k : ℕ, ∃ K : ℕ, 1 ≤ K ∧
      ∀ n : ℕ, (C : ℝ) * ((n : ℝ) + 1) ^ k *
        (2 : ℝ) ^ (α * (q : ℝ) * (n : ℝ)) ≤ (K : ℝ) * 2 ^ (p * n) := by
  obtain ⟨p, q, hp, hpq, hαpq⟩ := choose_integer_exponents α hα0 hα1
  refine ⟨p, q, hp, hpq, ?_⟩
  intro C k
  have ha : 0 ≤ (2 : ℝ) ^ (α * (q : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hb : 1 ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num)
  have hab : (2 : ℝ) ^ (α * (q : ℝ)) < (2 : ℝ) ^ p := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hαpq
  obtain ⟨K, hK, hbound⟩ := poly_exp_global_shifted
    ((2 : ℝ) ^ (α * (q : ℝ))) ((2 : ℝ) ^ p) k C ha hb hab
  refine ⟨K, hK, ?_⟩
  intro n
  simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), pow_mul] using hbound n

end PriorRoutes
