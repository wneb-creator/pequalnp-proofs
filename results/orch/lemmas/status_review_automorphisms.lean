import Lean
namespace PEqualNP.Outside.L_meta_2592_aux.Symmetries
def vertexMap (a v : Fin 10) : Fin 10 :=
  (([
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
  [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
  [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
  [3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
  [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
  [1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
  [2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
  [3, 2, 1, 6, 8, 4, 7, 0, 9, 5],
  [8, 3, 2, 1, 6, 5, 4, 7, 0, 9],
  [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]
] : List (List (Fin 10))).getD a.val []).getD v.val 0

def adjacent (u v : Fin 10) : Bool :=
  let edges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  edges.contains (u.val, v.val) || edges.contains (v.val, u.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem maps_are_automorphisms : ∀ a : Fin 10,
    vertexMap a a = 0 ∧
    (∀ u v : Fin 10, adjacent (vertexMap a u) (vertexMap a v) = adjacent u v) ∧
    (∀ u v : Fin 10, vertexMap a u = vertexMap a v → u = v) := by
  decide +kernel
end PEqualNP.Outside.L_meta_2592_aux.Symmetries
