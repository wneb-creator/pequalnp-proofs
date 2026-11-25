import Mathlib.Data.Finset.Powerset

namespace PEqualNP.Outside.L_meta_2585

lemma closed_incidence_test_criterion {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (I : α → β → Prop) [DecidableRel I]
    (f : (α → Bool) → (β → Bool) → Bool)
    (mono : ∀ x y x' y', (∀ a, x a = true → x' a = true) →
      (∀ b, y b = true → y' b = true) → f x y = true → f x' y' = true)
    (accepts : ∀ a b, I a b → f (fun a' => decide (a' = a))
      (fun b' => decide (b' = b)) = true)
    (rejects : ∀ S : Finset α,
      (∀ a, (∀ b, (∀ a' ∈ S, ¬ I a' b) → ¬ I a b) → a ∈ S) →
      f (fun a => decide (a ∈ S)) (fun b => decide (∀ a ∈ S, ¬ I a b)) = false) :
    ∀ x y, f x y = decide (∃ a b, I a b ∧ x a = true ∧ y b = true) := by
  intro x y
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hxy
    by_contra h
    let S : Finset α := Finset.univ.filter fun a => x a = true
    let T : Finset α := Finset.univ.filter fun a =>
      ∀ b, (∀ a' ∈ S, ¬ I a' b) → ¬ I a b
    have sub : ∀ a, a ∈ S → a ∈ T := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      exact hb a ha
    have same_lines (b : β) : (∀ a ∈ T, ¬ I a b) ↔ ∀ a ∈ S, ¬ I a b := by
      constructor
      · intro hb a ha
        exact hb a (sub a ha)
      · intro hb a ha
        exact (Finset.mem_filter.mp ha).2 b hb
    have closed : ∀ a, (∀ b, (∀ a' ∈ T, ¬ I a' b) → ¬ I a b) → a ∈ T := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      exact ha b ((same_lines b).mpr hb)
    have points : ∀ a, x a = true → decide (a ∈ T) = true := by
      intro a ha
      apply decide_eq_true
      apply sub
      simp [S, ha]
    have lines : ∀ b, y b = true → decide (∀ a ∈ T, ¬ I a b) = true := by
      intro b hb
      apply decide_eq_true
      apply (same_lines b).mpr
      intro a ha hab
      exact h ⟨a, b, hab, (Finset.mem_filter.mp ha).2, hb⟩
    have accepted := mono x y _ _ points lines hxy
    rw [rejects T closed] at accepted
    cases accepted
  · rintro ⟨a, b, hab, ha, hb⟩
    apply mono (fun a' => decide (a' = a)) (fun b' => decide (b' = b))
      x y ?_ ?_ (accepts a b hab)
    · intro a' ha'
      simp only [decide_eq_true_eq] at ha'
      subst a'
      exact ha
    · intro b' hb'
      simp only [decide_eq_true_eq] at hb'
      subst b'
      exact hb

end PEqualNP.Outside.L_meta_2585
