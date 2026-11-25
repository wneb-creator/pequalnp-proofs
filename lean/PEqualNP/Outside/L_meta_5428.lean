import Mathlib
import PEqualNP.Defs

-- L-meta-5428: the stated eight-gate circuit is checked gate by gate and on the sixteen inputs.

theorem PEqualNP.Outside.L_meta_5428 :
    PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit).size = 8 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (5807 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
