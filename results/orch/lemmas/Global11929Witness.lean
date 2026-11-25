import PEqualNP.Defs

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace PEqualNP.Outside.L_meta_11929.UpperWitness

open PEqualNP.CircuitLowerBounds

def edges : List ℕ := [0, 4, 1, 4, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def edgeFunction (x : Fin 7 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

def witness : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [5, 6]⟩,
   ⟨.or, [7, 5]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [10, 12]⟩,
   ⟨.or, [13, 14]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessCorrect : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witness, 15⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

theorem witnessSize : witness.length = 9 := rfl

end PEqualNP.Outside.L_meta_11929.UpperWitness
