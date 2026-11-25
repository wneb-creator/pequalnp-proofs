import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_matching_sanity

lemma matching_cover_lower (p : ℕ) (S : Finset (Fin (p + p)))
    (h : ∀ a : Fin p, Fin.castAdd p a ∈ S ∨ Fin.natAdd p a ∈ S) :
    p ≤ S.card := by
  classical
  let f : Fin p → Fin (p + p) := fun a =>
    if Fin.castAdd p a ∈ S then Fin.castAdd p a else Fin.natAdd p a
  have hf : Function.Injective f := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    dsimp [f] at hab
    split_ifs at hab <;>
      have hv := congrArg Fin.val hab <;>
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv <;>
      omega
  have hmem : ∀ a, f a ∈ S := by
    intro a
    dsimp [f]
    split_ifs with ha
    · exact ha
    · exact (h a).resolve_left ha
  have hs : Finset.univ.image f ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨a, _, rfl⟩
    exact hmem a
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf] at hc
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

end PEqualNP.Outside.L_meta_4675_matching_sanity
