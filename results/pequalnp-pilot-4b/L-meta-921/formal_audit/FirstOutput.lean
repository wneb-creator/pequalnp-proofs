import Mathlib

namespace Meta921Audit

variable {α : Type*}

theorem one_or_child_already_correct
    (L : Finset α) (k : ℕ) (hL : L.card ≤ k)
    (f g : Finset α → Prop) (hf : Monotone f) (hg : Monotone g)
    (hout : ∀ X : Finset α, X.card ≤ k → ((f X ∨ g X) ↔ L ⊆ X)) :
    (∀ X : Finset α, X.card ≤ k → (f X ↔ L ⊆ X)) ∨
    (∀ X : Finset α, X.card ≤ k → (g X ↔ L ⊆ X)) := by
  rcases (hout L hL).mpr (Finset.Subset.refl L) with hfl | hgl
  · left
    intro X hX
    constructor
    · intro hfx
      exact (hout X hX).mp (Or.inl hfx)
    · intro hLX
      exact hf hLX hfl
  · right
    intro X hX
    constructor
    · intro hgx
      exact (hout X hX).mp (Or.inr hgx)
    · intro hLX
      exact hg hLX hgl

end Meta921Audit
