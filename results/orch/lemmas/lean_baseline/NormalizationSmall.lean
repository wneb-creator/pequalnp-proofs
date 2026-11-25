import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Basic

namespace PEqualNP.Outside.L_meta_650

lemma pruneOrTests {α : Type*} (P N : Set α) (A B : α → Bool)
    (G : α → Bool → Bool)
    (hmono : ∀ x, G x false = true → G x true = true)
    (hs : ∀ x ∈ P, A x = true → B x = true)
    (hp : ∀ x ∈ P, G x (A x || B x) = true)
    (hn : ∀ x ∈ N, G x (A x || B x) = false) :
    (∀ x ∈ P, G x (B x) = true) ∧ (∀ x ∈ N, G x (B x) = false) := by
  constructor
  · intro x hx
    have hm := hmono x
    have hs' := hs x hx
    have hp' := hp x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all
  · intro x hx
    have hm := hmono x
    have hn' := hn x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all

lemma pruneAndTests {α : Type*} (P N : Set α) (A B : α → Bool)
    (G : α → Bool → Bool)
    (hmono : ∀ x, G x false = true → G x true = true)
    (hs : ∀ x ∈ N, A x = true → B x = true)
    (hp : ∀ x ∈ P, G x (A x && B x) = true)
    (hn : ∀ x ∈ N, G x (A x && B x) = false) :
    (∀ x ∈ P, G x (A x) = true) ∧ (∀ x ∈ N, G x (A x) = false) := by
  constructor
  · intro x hx
    have hm := hmono x
    have hp' := hp x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all
  · intro x hx
    have hm := hmono x
    have hs' := hs x hx
    have hn' := hn x hx
    cases ha : A x <;> cases hb : B x <;>
      cases h₀ : G x false <;> cases h₁ : G x true <;> simp_all

lemma pruneZeroTests {α : Type*} (P N : Set α) (A : α → Bool)
    (G : α → Bool → Bool)
    (hmono : ∀ x, G x false = true → G x true = true)
    (hz : ∀ x ∈ P, A x = false)
    (hp : ∀ x ∈ P, G x (A x) = true)
    (hn : ∀ x ∈ N, G x (A x) = false) :
    (∀ x ∈ P, G x false = true) ∧ (∀ x ∈ N, G x false = false) := by
  constructor
  · intro x hx
    simpa only [hz x hx] using hp x hx
  · intro x hx
    have hm := hmono x
    have hn' := hn x hx
    cases ha : A x <;> cases h₀ : G x false <;>
      cases h₁ : G x true <;> simp_all

end PEqualNP.Outside.L_meta_650
