import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.EdgeSupport

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

lemma left_inj {p l : ℕ} {a a' : Fin p}
    (h : Fin.castAdd l a = Fin.castAdd l a') : a = a' :=
  Fin.ext (congrArg (fun z : Fin (p + l) => z.val) h)

lemma right_inj {p l : ℕ} {b b' : Fin l}
    (h : Fin.natAdd p b = Fin.natAdd p b') : b = b' := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [Fin.val_natAdd] at hval
  omega

lemma edge_card_le_support_sum (p l : ℕ) (E : Finset (Fin p × Fin l))
    (U : Fin (p + l) → Finset (Fin (p + l)))
    (hcover : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ U (Fin.castAdd l a) ∨ Fin.castAdd l a ∈ U (Fin.natAdd p b)) :
    E.card ≤ ∑ c : Fin (p + l), (U c).card := by
  classical
  let f : Fin p × Fin l → Fin (p + l) × Fin (p + l) := fun e =>
    if Fin.natAdd p e.2 ∈ U (Fin.castAdd l e.1)
    then (Fin.castAdd l e.1, Fin.natAdd p e.2)
    else (Fin.natAdd p e.2, Fin.castAdd l e.1)
  have hf : Function.Injective f := by
    intro e e' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    by_cases hc : Fin.natAdd p e.2 ∈ U (Fin.castAdd l e.1)
    · by_cases hc' : Fin.natAdd p e'.2 ∈ U (Fin.castAdd l e'.1)
      · simp only [f, hc, hc', ↓reduceIte] at h1 h2
        exact Prod.ext (left_inj h1) (right_inj h2)
      · simp only [f, hc, hc', ↓reduceIte] at h1
        exact False.elim (left_ne_right e.1 e'.2 h1)
    · by_cases hc' : Fin.natAdd p e'.2 ∈ U (Fin.castAdd l e'.1)
      · simp only [f, hc, hc', ↓reduceIte] at h1
        exact False.elim (left_ne_right e'.1 e.2 h1.symm)
      · simp only [f, hc, hc', ↓reduceIte] at h1 h2
        exact Prod.ext (left_inj h2) (right_inj h1)
  let A : Finset (Fin (p + l) × Fin (p + l)) :=
    Finset.univ.biUnion fun c => (U c).image (fun v => (c, v))
  have hsub : E.image f ⊆ A := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    by_cases hc : Fin.natAdd p e.2 ∈ U (Fin.castAdd l e.1)
    · apply Finset.mem_biUnion.mpr
      exact ⟨Fin.castAdd l e.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨Fin.natAdd p e.2, hc, by simp [f, hc]⟩⟩
    · have he' := (hcover e.1 e.2 he).resolve_left hc
      apply Finset.mem_biUnion.mpr
      exact ⟨Fin.natAdd p e.2, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨Fin.castAdd l e.1, he', by simp [f, hc]⟩⟩
  calc
    E.card = (E.image f).card := (Finset.card_image_of_injective E hf).symm
    _ ≤ A.card := Finset.card_le_card hsub
    _ ≤ ∑ c : Fin (p + l), ((U c).image (fun v => (c, v))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ c : Fin (p + l), (U c).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

end PEqualNP.Outside.L_meta_4970.EdgeSupport
