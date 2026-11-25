import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

def edgePair {α β : Type} [DecidableEq α] [DecidableEq β]
    (u : α) (v : β) : α ⊕ β → Bool
  | .inl a => decide (a = u)
  | .inr b => decide (b = v)

def independentExtension {α β : Type} [Fintype α]
    (E : α → β → Prop) [DecidableRel E] (s : α → Bool) : α ⊕ β → Bool
  | .inl a => s a
  | .inr b => decide (∀ a, E a b → s a = false)

theorem bipartite_basis_correct {α β : Type} [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (E : α → β → Prop) [DecidableRel E]
    (f : (α ⊕ β → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) →
      f x = true → f y = true)
    (hpos : ∀ u v, E u v → f (edgePair u v) = true)
    (hneg : ∀ s, f (independentExtension E s) = false)
    (x : α ⊕ β → Bool) :
    f x = true ↔ ∃ u v, E u v ∧ x (.inl u) = true ∧ x (.inr v) = true := by
  constructor
  · intro hx
    by_contra hn
    have hle : ∀ i, x i = true →
        independentExtension E (fun a => x (.inl a)) i = true := by
      intro i hi
      cases i with
      | inl a => exact hi
      | inr b =>
        simp only [independentExtension, decide_eq_true_eq]
        intro a hab
        cases ha : x (.inl a) with
        | false => rfl
        | true => exact False.elim (hn ⟨a, b, hab, ha, hi⟩)
    have ht := hmono x _ hle hx
    rw [hneg] at ht
    contradiction
  · rintro ⟨u, v, huv, hu, hv⟩
    apply hmono (edgePair u v) x _ (hpos u v huv)
    intro i hi
    cases i with
    | inl a =>
      simp only [edgePair, decide_eq_true_eq] at hi
      simpa [hi] using hu
    | inr b =>
      simp only [edgePair, decide_eq_true_eq] at hi
      simpa [hi] using hv

end PEqualNP.Outside.L_meta_650
