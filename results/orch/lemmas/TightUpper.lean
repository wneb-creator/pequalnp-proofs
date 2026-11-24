import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4340_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperCircuit : Circuit :=
  ⟨[⟨.or, [9, 2]⟩, ⟨.and, [1, 10]⟩,
    ⟨.or, [3, 7]⟩, ⟨.and, [2, 12]⟩,
    ⟨.or, [3, 0]⟩, ⟨.and, [4, 14]⟩,
    ⟨.or, [0, 7]⟩, ⟨.and, [5, 16]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [18, 3]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [15, 17]⟩,
    ⟨.or, [21, 22]⟩, ⟨.or, [23, 20]⟩], 24⟩

lemma upper_size : upperCircuit.size = 15 := rfl

lemma upper_fan : FanInTwo upperCircuit := by
  simp [FanInTwo, upperCircuit]

lemma upper_leaf : ∀ g ∈ upperCircuit.gates,
    (∀ i ∈ g.inputs, i < 9) → g.op ≠ GateOp.and ∧ g.op ≠ GateOp.not := by
  simp [upperCircuit]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma upper_correct : ∀ x : Fin 9 → Bool,
    upperCircuit.eval (List.ofFn x ++ [x 0 || x 6]) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  decide +kernel

end PEqualNP.Outside.L_meta_4340_aux
