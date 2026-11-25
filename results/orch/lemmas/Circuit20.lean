import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

def petersenValue (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def petersenCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩, ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩, ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩, ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩, ⟨.or, [28, 24]⟩], 29⟩

lemma petersenCircuit_size : petersenCircuit.size = 20 := by rfl

lemma petersenCircuit_fanInTwo : PEqualNP.MetaComplexity.FanInTwo petersenCircuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, petersenCircuit]

lemma petersenCircuit_no_not :
    ∀ g ∈ petersenCircuit.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  simp [petersenCircuit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersenCircuit_correct :
    ∀ x : Fin 10 → Bool, petersenCircuit.eval (List.ofFn x) = petersenValue x := by
  decide

lemma petersen_has_size_twenty : PEqualNP.MetaComplexity.HasCircuitSize 10 petersenValue 20 := by
  exact ⟨petersenCircuit, petersenCircuit_fanInTwo, le_of_eq petersenCircuit_size,
    petersenCircuit_correct⟩

end PEqualNP.Outside.L_meta_2592
