import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def graph (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def witness : List Gate := [⟨.or, [0, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [18, 19]⟩]

lemma witness_length : witness.length = 14 := rfl

lemma witness_basis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_correct : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma graph_correct : ∀ x : Fin 7 → Bool, graph x = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10760
