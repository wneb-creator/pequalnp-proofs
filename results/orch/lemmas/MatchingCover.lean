import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

lemma matching_cover_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f)
    (he : ∀ a, (a, f a) ∈ E)
    (S : Finset (Fin (p + l)))
    (hS : ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) :
    p ≤ S.card := by
  classical
  let g : Fin p → Fin (p + l) := fun a =>
    if Fin.castAdd l a ∈ S then Fin.castAdd l a else Fin.natAdd p (f a)
  have hg : Function.Injective g := by
    intro a b hab
    dsimp only [g] at hab
    split_ifs at hab with ha hb
    · apply Fin.ext
      exact congrArg (fun v : Fin (p + l) => v.val) hab
    · have hv := congrArg Fin.val hab
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have := a.isLt
      omega
    · have hv := congrArg Fin.val hab
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have := b.isLt
      omega
    · apply hf
      apply Fin.ext
      have hv := congrArg Fin.val hab
      simp only [Fin.val_natAdd] at hv
      omega
  have hsub : Finset.univ.image g ⊆ S := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    dsimp only [g]
    split_ifs with ha
    · exact ha
    · exact (hS a (f a) (he a)).resolve_left ha
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin] using hcard

def subK4Edges : Finset (Fin 4 × Fin 6) :=
  {(0, 0), (1, 0), (0, 1), (2, 1), (0, 2), (3, 2),
   (1, 3), (2, 3), (1, 4), (3, 4), (2, 5), (3, 5)}

lemma subK4_no_four : ∀ (a a' : Fin 4) (b b' : Fin 6),
    a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ subK4Edges ∧ (a, b') ∈ subK4Edges ∧
      (a', b) ∈ subK4Edges ∧ (a', b') ∈ subK4Edges) := by
  decide

lemma subK4_edge_card : subK4Edges.card = 12 := by decide

lemma subK4_cover_card (S : Finset (Fin 10))
    (hS : ∀ (a : Fin 4) (b : Fin 6), (a, b) ∈ subK4Edges →
      Fin.castAdd 6 a ∈ S ∨ Fin.natAdd 4 b ∈ S) : 4 ≤ S.card := by
  apply matching_cover_card subK4Edges (![0, 3, 5, 2] : Fin 4 → Fin 6)
  · decide
  · decide
  · exact hS

end PEqualNP.Outside.L_meta_4970_aux
