import Mathlib

namespace PEqualNP.Outside.L_meta_4675.RestoreStar

def pairVal {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (v : α ⊕ β) : Bool :=
  decide (v = Sum.inl a ∨ v = Sum.inr b)

def graphValue {α β : Type*} (E : Finset (α × β)) (x : α ⊕ β → Bool) : Prop :=
  ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true

lemma pairVal_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (x : α ⊕ β → Bool) (a : α) (b : β)
    (ha : x (Sum.inl a) = true) (hb : x (Sum.inr b) = true) :
    ∀ v, pairVal a b v = true → x v = true := by
  intro v hv
  simp only [pairVal, decide_eq_true_eq] at hv
  rcases hv with hv | hv
  · simpa [hv] using ha
  · simpa [hv] using hb

lemma false_prune_restore_star {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A : Finset α) (B : Finset β)
    (b0 b1 : β) (q0 : α) (F0 : (α ⊕ β → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) →
      F0 x = true → F0 y = true)
    (hbelow : ∀ x, F0 x = true → graphValue E x)
    (houtside : ∀ a b, (a, b) ∈ E → (a ∉ A ∨ b ∉ B) →
      F0 (pairVal a b) = true)
    (hexception : F0 (pairVal q0 b0) = true)
    (hshape : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E →
      b = b1 ∨ a = q0 ∧ b = b0)
    (hcolumn : ∀ a ∈ A, (a, b1) ∈ E) :
    ∀ x, graphValue E x ↔
      F0 x = true ∨ (∃ a ∈ A, x (Sum.inl a) = true) ∧ x (Sum.inr b1) = true := by
  intro x
  constructor
  · rintro ⟨a, b, hab, hxa, hxb⟩
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ B
      · rcases hshape a ha b hb hab with hb1 | ⟨ha0, hb0⟩
        · exact Or.inr ⟨⟨a, ha, hxa⟩, hb1 ▸ hxb⟩
        · apply Or.inl
          apply hmono (pairVal q0 b0) x
          · apply pairVal_le
            · simpa [ha0] using hxa
            · simpa [hb0] using hxb
          · exact hexception
      · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
          (houtside a b hab (Or.inr hb)))
    · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
        (houtside a b hab (Or.inl ha)))
  · rintro (hx | ⟨⟨a, ha, hxa⟩, hxb⟩)
    · exact hbelow x hx
    · exact ⟨a, b1, hcolumn a ha, hxa, hxb⟩

end PEqualNP.Outside.L_meta_4675.RestoreStar
