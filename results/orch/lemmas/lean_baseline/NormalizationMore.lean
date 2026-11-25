import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Basic

namespace PEqualNP.Outside.L_meta_650

lemma pruneDominanceTests {α : Type*} (P N : Set α) (A B : α → Bool)
    (G : α → Bool → Bool)
    (hmono : ∀ x, G x false = true → G x true = true)
    (hpos : ∀ x ∈ P, A x = true → B x = true)
    (hneg : ∀ x ∈ N, B x = true → A x = true)
    (hp : ∀ x ∈ P, G x (A x) = true)
    (hn : ∀ x ∈ N, G x (A x) = false) :
    (∀ x ∈ P, G x (B x) = true) ∧ (∀ x ∈ N, G x (B x) = false) := by
  constructor
  · intro x hx
    have hm := hmono x
    have hs := hpos x hx
    have hp' := hp x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all
  · intro x hx
    have hm := hmono x
    have hs := hneg x hx
    have hn' := hn x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all

lemma pruneOneTests {α : Type*} (P N : Set α) (A : α → Bool)
    (G : α → Bool → Bool)
    (hmono : ∀ x, G x false = true → G x true = true)
    (ho : ∀ x ∈ N, A x = true)
    (hp : ∀ x ∈ P, G x (A x) = true)
    (hn : ∀ x ∈ N, G x (A x) = false) :
    (∀ x ∈ P, G x true = true) ∧ (∀ x ∈ N, G x true = false) := by
  constructor
  · intro x hx
    have hm := hmono x
    have hp' := hp x hx
    cases ha : A x <;> cases h₀ : G x false <;>
      cases h₁ : G x true <;> simp_all
  · intro x hx
    simpa only [ho x hx] using hn x hx

end PEqualNP.Outside.L_meta_650
