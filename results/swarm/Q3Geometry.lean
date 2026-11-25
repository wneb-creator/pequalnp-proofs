import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

def q3Coordinates : Fin 13 → Fin 3 × Fin 3 × Fin 3 :=
  ![(0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2),
    (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1),
    (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2)]

abbrev q3Incidence (p l : Fin 13) : Prop :=
  (q3Coordinates p).1 * (q3Coordinates l).1 +
    (q3Coordinates p).2.1 * (q3Coordinates l).2.1 +
    (q3Coordinates p).2.2 * (q3Coordinates l).2.2 = 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma q3_columns : ∀ l : Fin 13,
    (Finset.univ.filter (fun p => q3Incidence p l)).card = 3 + 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma q3_unique : ∀ p p' : Fin 13, p ≠ p' →
    ∃! l : Fin 13, q3Incidence p l ∧ q3Incidence p' l := by
  simp only [ExistsUnique]
  decide +kernel

end PEqualNP.Outside.L_meta_2583
