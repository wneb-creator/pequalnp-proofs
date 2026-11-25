import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_269

noncomputable def f : Polynomial ℝ :=
  Polynomial.monomial 0 1 + Polynomial.monomial 6 2048 + Polynomial.monomial 10 (-16384)
    + Polynomial.monomial 14 (1 / 512)

noncomputable def g : Polynomial ℝ :=
  Polynomial.monomial 0 (-1) + Polynomial.monomial 4 64 + Polynomial.monomial 8 (-32)
    + Polynomial.monomial 10 (1 / 16)

theorem card_add (p q : Polynomial ℝ) :
    (p + q).support.card ≤ p.support.card + q.support.card :=
  (Finset.card_le_card Polynomial.support_add).trans (Finset.card_union_le _ _)

theorem card_mono (n : ℕ) (a : ℝ) : (Polynomial.monomial n a).support.card ≤ 1 :=
  (Finset.card_le_card (Polynomial.support_monomial_subset n a)).trans (by simp)

theorem card_four (n1 n2 n3 n4 : ℕ) (a1 a2 a3 a4 : ℝ) :
    (Polynomial.monomial n1 a1 + Polynomial.monomial n2 a2 + Polynomial.monomial n3 a3
      + Polynomial.monomial n4 a4).support.card ≤ 4 := by
  have h1 := card_add (Polynomial.monomial n1 a1 + Polynomial.monomial n2 a2
    + Polynomial.monomial n3 a3) (Polynomial.monomial n4 a4)
  have h2 := card_add (Polynomial.monomial n1 a1 + Polynomial.monomial n2 a2)
    (Polynomial.monomial n3 a3)
  have h3 := card_add (Polynomial.monomial n1 a1) (Polynomial.monomial n2 a2)
  have k1 := card_mono n1 a1
  have k2 := card_mono n2 a2
  have k3 := card_mono n3 a3
  have k4 := card_mono n4 a4
  omega

theorem f_card : f.support.card ≤ 4 := card_four _ _ _ _ _ _ _ _

theorem g_card : g.support.card ≤ 4 := card_four _ _ _ _ _ _ _ _

theorem eval_p (x : ℝ) : (f * g + 1).eval x =
    (1 + 2048 * x ^ 6 - 16384 * x ^ 10 + 1 / 512 * x ^ 14)
      * (-1 + 64 * x ^ 4 - 32 * x ^ 8 + 1 / 16 * x ^ 10) + 1 := by
  simp only [f, g, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_monomial]
  ring

theorem p_ne : f * g + 1 ≠ 0 := by
  intro h
  have h1 := eval_p 1
  rw [h] at h1
  norm_num at h1

theorem root_in (a b : ℝ) (hab : a < b)
    (h : (f * g + 1).eval a * (f * g + 1).eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ c ∈ (f * g + 1).roots.toFinset := by
  have hc : ContinuousOn (fun x => (f * g + 1).eval x) (Set.Icc a b) :=
    (f * g + 1).continuous.continuousOn
  rcases lt_trichotomy ((f * g + 1).eval a) 0 with ha | ha | ha
  · have hb : 0 < (f * g + 1).eval b := by
      by_contra hn
      have := mul_nonneg_of_nonpos_of_nonpos ha.le (not_lt.mp hn)
      linarith
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    refine ⟨c, hc1.1, hc1.2, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots p_ne]
    exact hc2
  · rw [ha] at h
    simp at h
  · have hb : (f * g + 1).eval b < 0 := by
      by_contra hn
      have := mul_nonneg ha.le (not_lt.mp hn)
      linarith
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    refine ⟨c, hc1.1, hc1.2, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots p_ne]
    exact hc2

theorem step (S : Finset ℝ) (n : ℕ) (a b c : ℝ)
    (h : n ≤ (S.filter (fun x => x < a)).card)
    (hc : c ∈ S) (hac : a ≤ c) (hcb : c < b) :
    n + 1 ≤ (S.filter (fun x => x < b)).card := by
  have hsub : insert c (S.filter (fun x => x < a)) ⊆ S.filter (fun x => x < b) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact Finset.mem_filter.mpr ⟨hc, hcb⟩
    · have hx2 := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx2.1, by linarith [hx2.2]⟩
  have hnot : c ∉ S.filter (fun x => x < a) := by
    intro hx
    have hx2 := (Finset.mem_filter.mp hx).2
    linarith
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hle
  omega

theorem main : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 4 ∧ g.support.card ≤ 4) →
    ((f * g + 1).roots.toFinset).card ≤ 12) := by
  intro h
  have h12 := h f g ⟨f_card, g_card⟩
  obtain ⟨r1, a1, b1, m1⟩ := root_in (-54) (-23) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r2, a2, b2, m2⟩ := root_in (-23) (-2) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r3, a3, b3, m3⟩ := root_in (-2) (-1) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r4, a4, b4, m4⟩ := root_in (-1) (-(1 / 2)) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r5, a5, b5, m5⟩ := root_in (-(1 / 2)) (-(1 / 4)) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r6, a6, b6, m6⟩ := root_in (-(1 / 4)) (-(1 / 6)) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r7, a7, b7, m7⟩ := root_in (1 / 6) (1 / 4) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r8, a8, b8, m8⟩ := root_in (1 / 4) (1 / 2) (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r9, a9, b9, m9⟩ := root_in (1 / 2) 1 (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r10, a10, b10, m10⟩ := root_in 1 2 (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r11, a11, b11, m11⟩ := root_in 2 23 (by norm_num)
    (by simp only [eval_p]; norm_num)
  obtain ⟨r12, a12, b12, m12⟩ := root_in 23 54 (by norm_num)
    (by simp only [eval_p]; norm_num)
  have z : (0 : ℝ) ∈ (f * g + 1).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots p_ne, Polynomial.IsRoot, eval_p]
    norm_num
  have c0 : 0 ≤ (((f * g + 1).roots.toFinset).filter (fun x => x < (-54 : ℝ))).card :=
    Nat.zero_le _
  have c1 := step _ _ _ (-23) _ c0 m1 a1.le b1
  have c2 := step _ _ _ (-2) _ c1 m2 a2.le b2
  have c3 := step _ _ _ (-1) _ c2 m3 a3.le b3
  have c4 := step _ _ _ (-(1 / 2)) _ c3 m4 a4.le b4
  have c5 := step _ _ _ (-(1 / 4)) _ c4 m5 a5.le b5
  have c6 := step _ _ _ (-(1 / 6)) _ c5 m6 a6.le b6
  have c7 := step _ _ _ (1 / 6) _ c6 z (by norm_num) (by norm_num)
  have c8 := step _ _ _ (1 / 4) _ c7 m7 a7.le b7
  have c9 := step _ _ _ (1 / 2) _ c8 m8 a8.le b8
  have c10 := step _ _ _ 1 _ c9 m9 a9.le b9
  have c11 := step _ _ _ 2 _ c10 m10 a10.le b10
  have c12 := step _ _ _ 23 _ c11 m11 a11.le b11
  have c13 := step _ _ _ 54 _ c12 m12 a12.le b12
  have hfin := Finset.card_le_card
    (Finset.filter_subset (fun x => x < (54 : ℝ)) ((f * g + 1).roots.toFinset))
  omega

end PEqualNP.Outside.L_gct_269

theorem PEqualNP.Outside.L_gct_269 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 4 ∧ g.support.card ≤ 4) → ((f * g + 1).roots.toFinset).card ≤ 12) :=
  PEqualNP.Outside.L_gct_269.main
