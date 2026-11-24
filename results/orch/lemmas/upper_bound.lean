import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1677_aux

open PEqualNP.CircuitLowerBounds

def upper : Circuit :=
  ⟨[⟨.or, [0, 6]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [5, 16]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [22, 23]⟩], 24⟩

lemma upper_size : upper.size = 16 := rfl

lemma upper_fanin : PEqualNP.MetaComplexity.FanInTwo upper := by
  simp [PEqualNP.MetaComplexity.FanInTwo, upper]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upper_first : ∀ x : Fin 9 → Bool,
    (upper.wires (List.ofFn x)).getD 9 false = (x 0 || x 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upper_second : ∀ x : Fin 9 → Bool,
    (upper.wires (List.ofFn x)).getD 10 false = (x 1 || x 3) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upper_computes : ∀ x : Fin 9 → Bool,
    upper.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
       (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
       (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1677_aux
