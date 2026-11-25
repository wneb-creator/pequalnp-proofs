import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5429 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).size = 8 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (5071 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
