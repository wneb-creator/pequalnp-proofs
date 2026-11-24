import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1464 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    3 ≤ (S i0).card → (∀ i : Fin m, i ≠ i0 → (S i ∩ S i0).card ≤ 1) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, i ≠ i0 → f i ∈ S i0 ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ S i0, r (f i) y := by
  classical
  intro n m S i0 h3 hmeet
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < (S i0).card)
  let d : Fin n → Fin n := fun y => if y = a then b else if y = b then c else a
  have hdmem : ∀ y, d y ∈ S i0 := by
    intro y; simp only [d]; split_ifs <;> assumption
  have hd1 : ∀ y, d y ≠ y := by
    intro y; simp only [d]
    split_ifs with h1 h2
    · subst h1; exact hab.symm
    · subst h2; exact hbc.symm
    · exact fun h => h1 h.symm
  have hd2 : ∀ y, d (d y) ≠ y := by
    intro y
    by_cases h1 : y = a
    · subst h1; simp [d, hab.symm, hac.symm]
    · by_cases h2 : y = b
      · subst h2; simp [d, hab.symm, hbc.symm, hac.symm]
        exact hab
      · simp [d, h1, h2]
        exact fun h => h2 h.symm
  refine ⟨fun x y => x = d y,
    fun i => if h : (S i ∩ S i0).Nonempty then d h.choose else a, ?_, ?_⟩
  · intro x y hxy hyx
    exact hd2 y (by rw [← hxy]; exact hyx.symm)
  · intro i hi
    have hone := Finset.card_le_one.1 (hmeet i hi)
    by_cases h : (S i ∩ S i0).Nonempty
    · simp only [h, dif_pos]
      have hy0 := h.choose_spec
      refine ⟨hdmem _, ?_, ?_⟩
      · intro hin
        have := hone _ (Finset.mem_inter.2 ⟨hin, hdmem _⟩) _ hy0
        exact hd1 _ this
      · intro y hy
        rw [hone y hy _ hy0]
    · simp only [h, dif_neg, not_false_eq_true]
      refine ⟨ha, ?_, ?_⟩
      · intro hin
        exact h ⟨a, Finset.mem_inter.2 ⟨hin, ha⟩⟩
      · intro y hy
        exact absurd ⟨y, hy⟩ h
