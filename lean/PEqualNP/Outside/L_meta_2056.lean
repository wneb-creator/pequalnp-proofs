import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056

def reviewAdjacent (u v : Fin 26) : Prop :=
  (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9]) ∨
  (v.val < 13 ∧ 13 ≤ u.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9])

lemma reviewAdjacent_irrefl : ∀ u : Fin 26, ¬ reviewAdjacent u u := by
  unfold reviewAdjacent
  decide +kernel

lemma reviewAdjacent_symm : ∀ u v : Fin 26,
    reviewAdjacent u v ↔ reviewAdjacent v u := by
  unfold reviewAdjacent
  decide +kernel

set_option synthInstance.maxSize 1000 in
lemma reviewPrivateNeighbor : ∀ u v : Fin 26, u ≠ v →
    ∃ w : Fin 26, w ≠ v ∧ reviewAdjacent u w ∧ ¬ reviewAdjacent v w := by
  unfold reviewAdjacent
  decide +kernel

end PEqualNP.Outside.L_meta_2056
