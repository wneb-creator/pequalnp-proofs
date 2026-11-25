import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14985_aux

open PEqualNP.CircuitLowerBounds

def graphFn (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def graphWit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [6, 10]⟩,
    ⟨.or, [9, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [14, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [17, 16]⟩], 18⟩

lemma graphWitLegal : ∀ g ∈ graphWit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [graphWit]

lemma graphWitSize : graphWit.gates.length = 11 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma graphWitEval : ∀ x : Fin 8 → Bool, graphWit.eval (List.ofFn x) = graphFn x := by
  decide +kernel

end PEqualNP.Outside.L_meta_14985_aux
