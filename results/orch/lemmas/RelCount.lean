import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_2585_aux.OrBound

lemma card_le_of_unique_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, Set.Subsingleton {a | a ∈ s ∧ r a b}) : s.card ≤ t.card := by
  classical
  let f : s → β := fun a => Classical.choose (hs a.1 a.2)
  have hf (a : s) : f a ∈ t ∧ r a.1 (f a) := Classical.choose_spec (hs a.1 a.2)
  let g : s → t := fun a => ⟨f a, (hf a).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' heq
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply Subtype.ext
  exact ht (f a) (hf a).1 ⟨a.2, (hf a).2⟩ ⟨a'.2, heq'.symm ▸ (hf a').2⟩

end PEqualNP.Outside.L_meta_2585_aux.OrBound
