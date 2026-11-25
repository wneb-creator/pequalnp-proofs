import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_5393 : ∀ C D : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → D = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }], output := 11 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 6 C ∧ C.size = 10 ∧ PEqualNP.TopForm.IsAO2 6 D ∧ D.size = 6 ∧
  (∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = decide (∃ e ∈ ([(0, 4), (1, 4), (2, 4), (0, 5), (3, 5)] : List (Fin 6 × Fin 6)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 D x = decide (∃ e ∈ ([(0, 4), (1, 4), (2, 4), (0, 5), (3, 5)] : List (Fin 6 × Fin 6)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 4), (1, 4), (2, 4), (0, 5), (3, 5)] : List (Fin 6 × Fin 6)), PEqualNP.Core.ReadTwiceAt 6 C (C.output - 6) e.1 e.2 ↔ e ∈ ([(1, 4), (3, 5)] : List (Fin 6 × Fin 6))) := by
  intro C D hC hD
  subst hC hD
  refine ⟨by decide, rfl, by decide, rfl, ?_, ?_, ?_⟩
  · intro x
    revert x
    decide
  · intro x
    revert x
    decide
  · decide
