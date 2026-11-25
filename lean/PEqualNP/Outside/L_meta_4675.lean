import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

lemma cover_of_row_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + (E.image Prod.fst).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  let f : Fin p ↪ Fin (p + l) :=
    ⟨Fin.castAdd l, fun _ _ h => Fin.ext (congrArg (fun z : Fin (p + l) => z.val) h)⟩
  refine ⟨(E.image Prod.fst).map f, ?_, ?_⟩
  · intro a b hab
    left
    exact Finset.mem_map.mpr ⟨a, Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩, rfl⟩
  · simpa using h

lemma cover_of_column_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + (E.image Prod.snd).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  let f : Fin l ↪ Fin (p + l) :=
    ⟨Fin.natAdd p, fun _ _ h =>
      Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (p + l) => z.val) h))⟩
  refine ⟨(E.image Prod.snd).map f, ?_, ?_⟩
  · intro a b hab
    right
    exact Finset.mem_map.mpr ⟨b, Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩, rfl⟩
  · simpa using h

lemma cover_of_small_side_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + min p l ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  by_cases hp : p ≤ l
  · apply cover_of_row_bound
    have hc : (E.image Prod.fst).card ≤ p := by
      simpa using Finset.card_le_univ (E.image Prod.fst)
    have hm : min p l = p := Nat.min_eq_left hp
    omega
  · apply cover_of_column_bound
    have hc : (E.image Prod.snd).card ≤ l := by
      simpa using Finset.card_le_univ (E.image Prod.snd)
    have hl : min p l = l := Nat.min_eq_right (by omega)
    omega

lemma empty_edge_cover (p l s : ℕ) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ (∅ : Finset (Fin p × Fin l)) →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (∅ : Finset (Fin p × Fin l)).card + S.card ≤ s + 1 := by
  exact ⟨∅, by simp, by simp⟩

end PEqualNP.Outside.L_meta_4675
