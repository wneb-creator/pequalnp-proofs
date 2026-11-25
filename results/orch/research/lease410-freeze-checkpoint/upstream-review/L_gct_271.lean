import Mathlib

open Polynomial

namespace PEqualNP.Outside.L_gct_271

noncomputable def F : Polynomial ℝ :=
  X ^ 9 - C 120 * X ^ 7 + C 4368 * X ^ 5 - C 52480 * X ^ 3 + C 147456 * X

noncomputable def G : Polynomial ℝ :=
  X ^ 8 - C 84 * X ^ 6 + C 1974 * X ^ 4 - C 12916 * X ^ 2 + C 11025

noncomputable def H : Polynomial ℝ := F * G + 1

noncomputable def T (k : ℕ) : ℝ := (2 * (k : ℝ) - 15) / 2

lemma F_support_card : F.support.card ≤ 5 := by
  have hsub : F.support ⊆ {1, 3, 5, 7, 9} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h1, h3, h5, h7, h9⟩ := hmem
    simp [F, coeff_X_pow, coeff_C_mul, coeff_X, h1, h3, h5, h7, h9, Ne.symm h1, Ne.symm h3,
      Ne.symm h5, Ne.symm h7, Ne.symm h9]
  calc F.support.card ≤ ({1, 3, 5, 7, 9} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 5 := by decide

lemma G_support_card : G.support.card ≤ 5 := by
  have hsub : G.support ⊆ {0, 2, 4, 6, 8} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h0, h2, h4, h6, h8⟩ := hmem
    simp [G, coeff_X_pow, coeff_C_mul, coeff_C, h0, h2, h4, h6, h8, Ne.symm h0, Ne.symm h2,
      Ne.symm h4, Ne.symm h6, Ne.symm h8]
  calc G.support.card ≤ ({0, 2, 4, 6, 8} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 5 := by decide

lemma root_between (p : Polynomial ℝ) (a b : ℝ) (hab : a ≤ b)
    (h : p.eval a * p.eval b < 0) : ∃ r ∈ Set.Ioo a b, p.eval r = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨ha, hb⟩
    exact ⟨r, hr, by simpa using hr0⟩
  · have hb : p.eval b < 0 := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo' hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨hb, ha⟩
    exact ⟨r, hr, by simpa using hr0⟩

set_option maxHeartbeats 4000000 in
lemma H_sign (k : Fin 15) : H.eval (T k) * H.eval (T ((k : ℕ) + 1)) < 0 := by
  fin_cases k <;>
    simp [H, F, G, T, eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one] <;>
    norm_num

lemma H_ne_zero : H ≠ 0 := by
  intro h
  have := H_sign 0
  simp [h] at this

lemma exists_roots : ∃ s : Finset ℝ, s.card = 15 ∧ ∀ x ∈ s, x ∈ H.roots.toFinset := by
  have hr : ∀ k : Fin 15, ∃ r ∈ Set.Ioo (T k) (T ((k : ℕ) + 1)), H.eval r = 0 := by
    intro k
    apply root_between
    · unfold T
      push_cast
      linarith
    · exact H_sign k
  choose r hr hr0 using hr
  have hmono : StrictMono r := by
    intro i j hij
    have h1 : r i < T ((i : ℕ) + 1) := (hr i).2
    have h2 : T (j : ℕ) < r j := (hr j).1
    have h3 : T ((i : ℕ) + 1) ≤ T (j : ℕ) := by
      unfold T
      have h4 : (i : ℕ) + 1 ≤ (j : ℕ) := hij
      have h5 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast
      linarith
    linarith
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective]
    simp
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots H_ne_zero]
    exact hr0 i

end PEqualNP.Outside.L_gct_271

theorem PEqualNP.Outside.L_gct_271 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 5 ∧ g.support.card ≤ 5) → ((f * g + 1).roots.toFinset).card ≤ 14) := by
  intro hall
  have hb := hall PEqualNP.Outside.L_gct_271.F PEqualNP.Outside.L_gct_271.G
    ⟨PEqualNP.Outside.L_gct_271.F_support_card, PEqualNP.Outside.L_gct_271.G_support_card⟩
  obtain ⟨s, hs, hsub⟩ := PEqualNP.Outside.L_gct_271.exists_roots
  have hle : s.card ≤ (PEqualNP.Outside.L_gct_271.H.roots.toFinset).card :=
    Finset.card_le_card (fun x hx => hsub x hx)
  have hb' : (PEqualNP.Outside.L_gct_271.H.roots.toFinset).card ≤ 14 := hb
  omega
