import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def upperCircuit : Circuit :=
  ⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [15, 8]⟩,
    ⟨.and, [3, 16]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [18, 9]⟩,
    ⟨.and, [7, 19]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.and, [8, 21]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [9, 23]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩
  ], 29⟩

lemma upperCircuit_size : upperCircuit.size = 20 := by rfl

lemma upperCircuit_fanInTwo : FanInTwo upperCircuit := by
  simp [FanInTwo, upperCircuit]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma upperCircuit_correct : ∀ x : Fin 10 → Bool,
    upperCircuit.eval (List.ofFn x) = edgeFunction x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592
