import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

def incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_diagonal (p : Fin 13) : incidence p p :=
  Or.inl rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
lemma incidence_no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → l ≠ m → incidence p l → incidence p m → incidence q l →
    ¬ incidence q m := by
  unfold incidence
  decide

lemma incidence_point_degree : ∀ p : Fin 13,
    ((Finset.univ : Finset (Fin 13)).filter
      (fun l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)).card = 4 := by
  decide

lemma incidence_line_degree : ∀ l : Fin 13,
    ((Finset.univ : Finset (Fin 13)).filter
      (fun p => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)).card = 4 := by
  decide

lemma incidence_edge_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3 ∨
        e.1 = e.2 + 9)).card = 52 := by
  decide

lemma incidence_deleted_edge_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => e.1 ≠ 0 ∧ e.2 ≠ 0 ∧
        (e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3 ∨
          e.1 = e.2 + 9))).card = 45 := by
  decide

lemma incidence_deleted_cover_bound (P L : Finset (Fin 13))
    (cover : ∀ p l : Fin 13, p ≠ 0 → l ≠ 0 → incidence p l → p ∈ P ∨ l ∈ L) :
    12 ≤ P.card + L.card := by
  have sub : (Finset.univ.erase 0 : Finset (Fin 13)) ⊆ P ∪ L := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_union.mpr (cover i i hi0 hi0 (incidence_diagonal i))
  calc
    12 = (Finset.univ.erase 0 : Finset (Fin 13)).card := by decide
    _ ≤ (P ∪ L).card := Finset.card_le_card sub
    _ ≤ P.card + L.card := Finset.card_union_le P L

end PEqualNP.Outside.L_meta_2602_aux
