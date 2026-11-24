import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma cover_lower : ∀ s : Finset (Fin 9),
    ((0 ∈ s ∨ 1 ∈ s) ∧
      (1 ∈ s ∨ 2 ∈ s) ∧
      (2 ∈ s ∨ 3 ∈ s) ∧
      (3 ∈ s ∨ 4 ∈ s) ∧
      (4 ∈ s ∨ 0 ∈ s) ∧
      (0 ∈ s ∨ 5 ∈ s) ∧
      (1 ∈ s ∨ 6 ∈ s) ∧
      (2 ∈ s ∨ 7 ∈ s) ∧
      (3 ∈ s ∨ 8 ∈ s) ∧
      (5 ∈ s ∨ 7 ∈ s) ∧
      (6 ∈ s ∨ 8 ∈ s) ∧
      (8 ∈ s ∨ 5 ∈ s)) → 5 ≤ s.card := by
  decide

def upperCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [9, 6]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [16, 8]⟩,
    ⟨.and, [5, 17]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [21, 15]⟩,
    ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩], 24⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma upper_bound : HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨upperCircuit, ?_, ?_, ?_⟩
  · simp [upperCircuit, FanInTwo]
  · decide
  · decide

end PEqualNP.Outside.L_meta_670
