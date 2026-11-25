import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def upperCircuit : Circuit := {
  gates := [
    ⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩]
  output := 29 }

lemma upperCircuit_fan : FanInTwo upperCircuit := by
  simp [FanInTwo, upperCircuit]

lemma upperCircuit_size : upperCircuit.size = 20 := rfl

lemma upperCircuit_noNot : ∀ g ∈ upperCircuit.gates, g.op ≠ GateOp.not := by
  simp [upperCircuit]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma upperCircuit_eval : ∀ x : Fin 10 → Bool,
    upperCircuit.eval (List.ofFn x) = petersen x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.Outside.L_meta_2592_aux in
theorem PEqualNP.Outside.L_meta_2592_upper :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 20 ∧
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x := by
  exact ⟨upperCircuit, upperCircuit_fan, upperCircuit_size,
    upperCircuit_noNot, upperCircuit_eval⟩
