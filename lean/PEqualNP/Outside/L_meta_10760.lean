import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def witness : List Gate := [
  ⟨.or, [0, 2]⟩,
  ⟨.or, [7, 1]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.and, [8, 4]⟩,
  ⟨.and, [0, 9]⟩,
  ⟨.and, [3, 5]⟩,
  ⟨.and, [7, 6]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.or, [17, 14]⟩,
  ⟨.or, [18, 15]⟩,
  ⟨.or, [19, 16]⟩]

lemma witness_basis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

lemma witness_length : witness.length = 14 := rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma witness_correct : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10760
