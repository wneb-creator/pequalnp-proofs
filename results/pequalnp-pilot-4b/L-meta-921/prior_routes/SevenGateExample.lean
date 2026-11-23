import Mathlib
import PEqualNP.Defs

namespace PriorRoutes.Meta921
open PEqualNP.CircuitLowerBounds

def exampleGates : List Gate := [
  ⟨.and, [4, 5]⟩,
  ⟨.and, [7, 6]⟩,
  ⟨.or, [1, 8]⟩,
  ⟨.and, [0, 9]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.and, [10, 8]⟩]

def firstLine : Finset (Fin 7) := {0, 1, 2, 3}
def secondLine : Finset (Fin 7) := {0, 4, 5, 6}
def lineInput (S : Finset (Fin 7)) : List Bool := List.ofFn (fun i => decide (i ∈ S))

theorem example_gate_count : exampleGates.length = 7 := rfl

theorem example_binary_monotone : ∀ g ∈ exampleGates,
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  simp [exampleGates]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem example_correct : ∀ x : Fin 7 → Bool,
    (Finset.univ.filter (fun i => x i = true)).card ≤ 5 →
    Circuit.eval ⟨exampleGates, 12⟩ (List.ofFn x) =
        decide (∀ i ∈ firstLine, x i = true) ∧
    Circuit.eval ⟨exampleGates, 13⟩ (List.ofFn x) =
        decide (∀ i ∈ secondLine, x i = true) := by
  decide

def privateToFirst : Finset (Fin 7) := Finset.univ.filter (fun j =>
  (Circuit.wires ⟨exampleGates, 12⟩ (lineInput firstLine)).getD (7 + j.val) false = true ∧
  (Circuit.wires ⟨exampleGates, 12⟩ (lineInput secondLine)).getD (7 + j.val) false = false)

theorem only_two_private_to_first : privateToFirst.card = 2 := by decide

end PriorRoutes.Meta921
