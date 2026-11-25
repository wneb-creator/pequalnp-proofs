import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def symTarget (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def symMap : Fin 12 → Fin 9 → Fin 9 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![0, 5, 8, 3, 4, 1, 7, 6, 2],
    ![1, 0, 5, 8, 6, 2, 4, 7, 3],
    ![1, 2, 3, 8, 6, 0, 7, 4, 5],
    ![2, 1, 0, 5, 7, 3, 6, 4, 8],
    ![2, 3, 8, 5, 7, 1, 4, 6, 0],
    ![3, 2, 1, 0, 4, 8, 7, 6, 5],
    ![3, 8, 5, 0, 4, 2, 6, 7, 1],
    ![5, 0, 1, 2, 7, 8, 4, 6, 3],
    ![5, 8, 3, 2, 7, 0, 6, 4, 1],
    ![8, 3, 2, 1, 6, 5, 4, 7, 0],
    ![8, 5, 0, 1, 6, 3, 7, 4, 2]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma sym_bijective : ∀ k : Fin 12, Function.Bijective (symMap k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma sym_invariant : ∀ (k : Fin 12) (x : Fin 9 → Bool),
    symTarget (x ∘ symMap k) = symTarget x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma sym_vertex_cover : ∀ a : Fin 9, ∃ k : Fin 12,
    symMap k a ∈ ([0, 4] : List (Fin 9)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma sym_pair_cover : ∀ a b : Fin 9, a ≠ b → ∃ k : Fin 12,
    (symMap k a, symMap k b) ∈
      ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)) ∨
    (symMap k b, symMap k a) ∈
      ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_670
