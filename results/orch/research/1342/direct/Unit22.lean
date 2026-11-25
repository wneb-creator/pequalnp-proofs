import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1342.Direct

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A checked near witness: size22, not the posted size21 conclusion.
def unit22 : Circuit :=
  ⟨[⟨GateOp.or, [8, 0]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.and, [1, 16]⟩,
    ⟨GateOp.or, [2, 14]⟩,
    ⟨GateOp.and, [5, 18]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [20, 10]⟩,
    ⟨GateOp.and, [6, 21]⟩,
    ⟨GateOp.or, [3, 9]⟩,
    ⟨GateOp.and, [7, 23]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [25, 4]⟩,
    ⟨GateOp.and, [10, 26]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [28, 19]⟩,
    ⟨GateOp.or, [29, 22]⟩,
    ⟨GateOp.or, [30, 24]⟩,
    ⟨GateOp.or, [31, 27]⟩], 32⟩

theorem unit22_mono : Monotone2 unit22 := by
  simp [Monotone2, unit22]

theorem unit22_size : unit22.size = 22 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unit22_exact : ∀ x : Fin 11 → Bool,
  unit22.eval (List.ofFn x) = true ↔
  ∃ u v : Fin 11, (u.val, v.val) ∈
    ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1342.Direct
