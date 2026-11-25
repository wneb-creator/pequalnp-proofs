import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.StressSymmetry

open PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0, 3), (1, 2), (0, 4), (2, 4), (1, 5),
    (3, 5), (0, 6), (1, 6), (2, 7), (3, 7)]

def table : List (List ℕ) := [
    [0, 1, 2, 3, 4, 5, 6, 7],
    [0, 2, 1, 3, 6, 7, 4, 5],
    [1, 0, 3, 2, 5, 4, 6, 7],
    [1, 3, 0, 2, 6, 7, 5, 4],
    [2, 0, 3, 1, 7, 6, 4, 5],
    [2, 3, 0, 1, 4, 5, 7, 6],
    [3, 1, 2, 0, 7, 6, 5, 4],
    [3, 2, 1, 0, 5, 4, 7, 6]]

def permutation (i v : Fin 8) : Fin 8 :=
  Fin.ofNat 8 ((table.getD i.val []).getD v.val 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
lemma automorphisms :
    ∀ i : Fin 8, Function.Bijective (permutation i) ∧
      ∀ u v : Fin 8, graph.Adj (permutation i u) (permutation i v) ↔ graph.Adj u v := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
lemma composition :
    ∀ i j : Fin 8, ∃ k : Fin 8, ∀ v : Fin 8,
      permutation k v = permutation i (permutation j v) := by
  decide

lemma identity : ∀ v : Fin 8, permutation 0 v = v := by
  decide

end PEqualNP.Outside.L_meta_1772_aux.StressSymmetry
