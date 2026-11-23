import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.FP3Strategy

open PEqualNP.Library

lemma alt_three (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔
      ∃ y₁ : List Bool, y₁.length = s ∧
        ∀ y₂ : List Bool, y₂.length = s →
          ∃ y₃ : List Bool, y₃.length = s ∧ P (y₁ ++ y₂ ++ y₃) := by
  simp [Alt, List.append_assoc]

lemma alt_constant (j s : ℕ) (P : Prop) : Alt j s (fun _ => P) ↔ P := by
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    simp only [Alt, ih, not_not]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      exact ⟨List.replicate s false, by simp, h⟩

lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    omega

lemma no_constant_absorption (p q K : ℕ) (hp : 1 ≤ p) (hpq : p < q) :
    ∃ n : ℕ, K * 2 ^ (p * n) + K < 2 ^ (q * n) := by
  let n := K + 1
  have hq : (p + 1) * n ≤ q * n := Nat.mul_le_mul_right n (by omega)
  have hpn : n ≤ p * n := by nlinarith
  have hx : K + 2 ≤ 2 ^ n := succ_le_two_pow n
  have ha : 2 ^ n ≤ 2 ^ (p * n) := Nat.pow_le_pow_right (by decide) hpn
  have hb : 2 ^ ((p + 1) * n) ≤ 2 ^ (q * n) :=
    Nat.pow_le_pow_right (by decide) hq
  rw [Nat.add_mul, one_mul, pow_add] at hb
  refine ⟨n, ?_⟩
  nlinarith

lemma adaptive_answers_do_not_commit :
    (∀ query : Bool, ∃ answer : Bool, answer = query) ∧
      ¬ (∃ answer : Bool, ∀ query : Bool, answer = query) := by
  constructor
  · intro query
    exact ⟨query, rfl⟩
  · rintro ⟨answer, h⟩
    have hf := h false
    have ht := h true
    cases hf.symm.trans ht

lemma local_path_checks_do_not_glue :
    (∀ edge : Fin 2, ∃ middle : Bool,
      (edge = 0 → middle = false) ∧ (edge = 1 → middle = true)) ∧
      ¬ (∃ middle : Bool, middle = false ∧ middle = true) := by
  constructor
  · intro edge
    fin_cases edge
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩
  · rintro ⟨middle, hf, ht⟩
    cases hf.symm.trans ht

lemma square_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

lemma no_linear_factor_absorption (p q K : ℕ) (hpq : p < q) :
    ∃ n : ℕ, (K * 2 ^ (p * n) + K) * (q * n) < 2 ^ (q * n) := by
  let n := 2 * K * q + 4
  have hn : 4 ≤ n := by omega
  have hsq : n * n ≤ 2 ^ n := square_le_two_pow n hn
  have hexp : 2 * K * q * n < 2 ^ n := by
    have hn' : 2 * K * q + 4 = n := rfl
    nlinarith
  have hbase : 1 ≤ 2 ^ (p * n) := Nat.one_le_two_pow
  have hq : (p + 1) * n ≤ q * n := Nat.mul_le_mul_right n (by omega)
  have hpow : 2 ^ ((p + 1) * n) ≤ 2 ^ (q * n) :=
    Nat.pow_le_pow_right (by decide) hq
  rw [Nat.add_mul, one_mul, pow_add] at hpow
  refine ⟨n, ?_⟩
  calc
    (K * 2 ^ (p * n) + K) * (q * n) ≤
        (2 * K * 2 ^ (p * n)) * (q * n) := by
      apply Nat.mul_le_mul_right
      nlinarith
    _ = 2 ^ (p * n) * (2 * K * q * n) := by ring
    _ < 2 ^ (p * n) * 2 ^ n := Nat.mul_lt_mul_of_pos_left hexp (by omega)
    _ ≤ 2 ^ (q * n) := hpow

end PEqualNP.Outside.FP3Strategy
