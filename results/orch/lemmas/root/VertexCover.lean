import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
   (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma petersen_vertex_cover_lower : ∀ c : Fin 10 → Bool,
    (∀ e ∈ petersenEdges, c e.1 || c e.2 = true) →
    6 ≤ (List.ofFn c).count true := by
  decide

end PEqualNP.Outside.L_meta_2592_aux
