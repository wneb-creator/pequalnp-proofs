import Mathlib

namespace PEqualNP.Outside.L_meta_4675

lemma linear_and_prune {α : Type*} [DecidableEq α]
    (A : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ a, x a = true → y a = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ a, x a = true → y a = true) → g x = true → g y = true)
    (hfg : ∀ x, (f x && g x) = decide (∃ a ∈ A, x a = true)) :
    (∀ x, f x = decide (∃ a ∈ A, x a = true)) ∨
      (∀ x, g x = decide (∃ a ∈ A, x a = true)) := by
  classical
  let z : α → Bool := fun a => decide (a ∉ A)
  have hz : ¬ ∃ a ∈ A, z a = true := by simp [z]
  have off : f z = false ∨ g z = false := by
    have h := hfg z
    simpa only [hz, decide_false, Bool.and_eq_false_iff] using h
  have prune (q : (α → Bool) → Bool)
      (hq : ∀ x y, (∀ a, x a = true → y a = true) → q x = true → q y = true)
      (hoff : q z = false)
      (hon : ∀ x, (∃ a ∈ A, x a = true) → q x = true) :
      ∀ x, q x = decide (∃ a ∈ A, x a = true) := by
    intro x
    by_cases hx : ∃ a ∈ A, x a = true
    · simpa [hx] using hon x hx
    · have xz : ∀ a, x a = true → z a = true := by
        intro a ha
        simp only [z, decide_eq_true_eq]
        exact fun hA => hx ⟨a, hA, ha⟩
      have hqx : q x = false := by
        cases h : q x with
        | false => rfl
        | true =>
          have h' := hq x z xz h
          simp [hoff] at h'
      simpa [hx] using hqx
  rcases off with hoff | hoff
  · apply Or.inl
    apply prune f hf hoff
    intro x hx
    have h := hfg x
    simp only [hx, decide_true, Bool.and_eq_true] at h
    exact h.1
  · apply Or.inr
    apply prune g hg hoff
    intro x hx
    have h := hfg x
    simp only [hx, decide_true, Bool.and_eq_true] at h
    exact h.2

end PEqualNP.Outside.L_meta_4675
