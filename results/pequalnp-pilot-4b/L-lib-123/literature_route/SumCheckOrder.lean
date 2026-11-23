import Mathlib

namespace PEqualNP.Outside.LiteratureRoute

open Polynomial

lemma late_sumcheck_cheats (F : Type*) [Field F] [CharP F 2] :
    ∀ r : F, ∃ g : Polynomial F,
      g.natDegree ≤ 1 ∧ g.eval 0 + g.eval 1 = 1 ∧ g.eval r = 0 := by
  intro r
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdouble : r + r = 0 := by
    calc
      r + r = (2 : F) * r := by ring
      _ = 0 := by rw [htwo, zero_mul]
  refine ⟨X - C r, ?_, ?_, ?_⟩
  · simp
  · simp only [eval_sub, eval_X, eval_C, zero_sub]
    linear_combination -hdouble
  · simp

lemma early_sumcheck_cannot_cheat (F : Type*) [Field F] :
    ¬ ∃ g : Polynomial F,
      g.eval 0 + g.eval 1 = 1 ∧ ∀ r : F, g.eval r = 0 := by
  rintro ⟨g, hsum, hzero⟩
  have h0 := hzero 0
  have h1 := hzero 1
  rw [h0, h1, zero_add] at hsum
  exact zero_ne_one hsum

lemma late_sumcheck_any_claim (F : Type*) [Field F] [CharP F 2] (c r : F) :
    ∃ g : Polynomial F,
      g.natDegree ≤ 1 ∧ g.eval 0 + g.eval 1 = c ∧ g.eval r = 0 := by
  obtain ⟨h, hd, hs, hr⟩ := late_sumcheck_cheats F r
  refine ⟨C c * h, ?_, ?_, ?_⟩
  · calc
      (C c * h).natDegree ≤ (C c).natDegree + h.natDegree := natDegree_mul_le
      _ ≤ 1 := by simpa using hd
  · simp only [eval_mul, eval_C]
    rw [← mul_add, hs, mul_one]
  · simp only [eval_mul, eval_C, hr, mul_zero]

lemma flattened_two_round_sumcheck_accepts_false (F : Type*) [Field F] [CharP F 2] :
    ∃ g₁ : Polynomial F, g₁.natDegree ≤ 1 ∧ g₁.eval 0 + g₁.eval 1 = 1 ∧
      ∀ r₁ r₂ : F, ∃ g₂ : Polynomial F,
        g₂.natDegree ≤ 1 ∧ g₂.eval 0 + g₂.eval 1 = g₁.eval r₁ ∧ g₂.eval r₂ = 0 := by
  refine ⟨X, by simp, by simp, ?_⟩
  intro r₁ r₂
  simpa using late_sumcheck_any_claim F r₁ r₂

lemma sequential_two_round_sumcheck_rejects_false (F : Type*) [Field F] :
    ¬ ∃ g₁ : Polynomial F, g₁.natDegree ≤ 1 ∧ g₁.eval 0 + g₁.eval 1 = 1 ∧
      ∀ r₁ : F, ∃ g₂ : Polynomial F,
        g₂.natDegree ≤ 1 ∧ g₂.eval 0 + g₂.eval 1 = g₁.eval r₁ ∧
          ∀ r₂ : F, g₂.eval r₂ = 0 := by
  rintro ⟨g₁, _, hsum, hround⟩
  apply early_sumcheck_cannot_cheat F
  refine ⟨g₁, hsum, ?_⟩
  intro r₁
  obtain ⟨g₂, _, hs, hz⟩ := hround r₁
  have h0 := hz 0
  have h1 := hz 1
  simpa [h0, h1] using hs.symm

lemma partial_sum_certificate {I F : Type*} [CommSemiring F]
    (s : Finset F) (t : Finset I) (f : I → Polynomial F) (D : ℕ)
    (hdegree : ∀ i ∈ t, (f i).natDegree ≤ D) (claim : F) :
    (∑ x ∈ s, ∑ i ∈ t, (f i).eval x) = claim ↔
      ∃ g : Polynomial F, g.natDegree ≤ D ∧
        (∑ x ∈ s, g.eval x) = claim ∧
        ∀ r : F, g.eval r = ∑ i ∈ t, (f i).eval r := by
  have heval (r : F) : (∑ i ∈ t, f i).eval r = ∑ i ∈ t, (f i).eval r := by
    exact map_sum (evalRingHom r) f t
  constructor
  · intro hsum
    refine ⟨∑ i ∈ t, f i, natDegree_sum_le_of_forall_le t f hdegree, ?_, heval⟩
    simpa only [heval] using hsum
  · rintro ⟨g, _, hsum, hcheck⟩
    simpa only [hcheck] using hsum

end PEqualNP.Outside.LiteratureRoute
