import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux.FlagComponents

lemma edge_in_flag {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β))
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (P : Finset α) (Q : Finset β) (a₀ : α) (b₀ : β)
    (ha₀ : a₀ ∈ P) (hP : ∀ a ∈ P, (a,b₀) ∈ E)
    (hQ : ∀ b ∈ Q, (a₀,b) ∈ E)
    {a : α} {b : β} (ha : a ∈ P) (hb : b ∈ Q) (he : (a,b) ∈ E) :
    a = a₀ ∨ b = b₀ := by
  by_contra h
  push_neg at h
  exact h4 a a₀ b b₀ h.1 h.2 ⟨he, hP a ha, hQ b hb, hP a₀ ha₀⟩

lemma component_of_flag {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β))
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (P : Finset α) (Q : Finset β) (a₀ : α) (b₀ : β)
    (ha₀ : a₀ ∈ P) (hP : ∀ a ∈ P, (a,b₀) ∈ E)
    (hQ : ∀ b ∈ Q, (a₀,b) ∈ E)
    (component : α × β → γ) (k : γ)
    (hPk : ∀ a ∈ P, component (a,b₀) = k)
    (hQk : ∀ b ∈ Q, component (a₀,b) = k)
    {a : α} {b : β} (ha : a ∈ P) (hb : b ∈ Q) (he : (a,b) ∈ E) :
    component (a,b) = k := by
  rcases edge_in_flag E h4 P Q a₀ b₀ ha₀ hP hQ ha hb he with rfl | rfl
  · exact hQk b hb
  · exact hPk a ha

lemma owner_of_two_leaves {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β))
    (h4 : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (S : Finset β) (hS : 2 ≤ S.card) (a a' : α)
    (ha : ∀ b ∈ S, (a,b) ∈ E) (ha' : ∀ b ∈ S, (a',b) ∈ E) : a = a' := by
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp hS
  by_contra hne
  exact h4 a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

end PEqualNP.Outside.L_meta_4970_aux.FlagComponents
