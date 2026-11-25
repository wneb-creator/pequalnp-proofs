import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edges : List ℕ :=
  [0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6]

def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

def witnessGates : List Gate :=
  [⟨.or, [0, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [7, 8]⟩,
   ⟨.and, [6, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 11]⟩,
   ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩,
   ⟨.or, [0, 4]⟩, ⟨.and, [2, 16]⟩, ⟨.or, [10, 12]⟩,
   ⟨.or, [15, 17]⟩, ⟨.or, [18, 19]⟩]

lemma witness_basis : ∀ g ∈ witnessGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witness_size : witnessGates.length = 14 := rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witnessGates, 20⟩ (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_10760
