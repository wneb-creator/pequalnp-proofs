import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def baseline : Circuit :=
  ⟨[
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [26, 16]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.and, [0, 28]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [30, 21]⟩,
    ⟨GateOp.or, [31, 25]⟩,
    ⟨GateOp.and, [1, 32]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [34, 24]⟩,
    ⟨GateOp.or, [35, 25]⟩,
    ⟨GateOp.and, [2, 36]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [38, 23]⟩,
    ⟨GateOp.or, [39, 24]⟩,
    ⟨GateOp.and, [3, 40]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [42, 23]⟩,
    ⟨GateOp.or, [43, 25]⟩,
    ⟨GateOp.and, [4, 44]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [46, 22]⟩,
    ⟨GateOp.or, [47, 24]⟩,
    ⟨GateOp.and, [5, 48]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.or, [50, 21]⟩,
    ⟨GateOp.or, [51, 23]⟩,
    ⟨GateOp.and, [6, 52]⟩,
    ⟨GateOp.or, [15, 19]⟩,
    ⟨GateOp.or, [54, 20]⟩,
    ⟨GateOp.or, [55, 22]⟩,
    ⟨GateOp.and, [7, 56]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [58, 19]⟩,
    ⟨GateOp.or, [59, 21]⟩,
    ⟨GateOp.and, [8, 60]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [62, 18]⟩,
    ⟨GateOp.or, [63, 20]⟩,
    ⟨GateOp.and, [9, 64]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [66, 19]⟩,
    ⟨GateOp.or, [67, 25]⟩,
    ⟨GateOp.and, [10, 68]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [70, 18]⟩,
    ⟨GateOp.or, [71, 24]⟩,
    ⟨GateOp.and, [11, 72]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [74, 17]⟩,
    ⟨GateOp.or, [75, 23]⟩,
    ⟨GateOp.and, [12, 76]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [78, 37]⟩,
    ⟨GateOp.or, [79, 41]⟩,
    ⟨GateOp.or, [80, 45]⟩,
    ⟨GateOp.or, [81, 49]⟩,
    ⟨GateOp.or, [82, 53]⟩,
    ⟨GateOp.or, [83, 57]⟩,
    ⟨GateOp.or, [84, 61]⟩,
    ⟨GateOp.or, [85, 65]⟩,
    ⟨GateOp.or, [86, 69]⟩,
    ⟨GateOp.or, [87, 73]⟩,
    ⟨GateOp.or, [88, 77]⟩
  ], 89⟩

lemma baseline_size : baseline.size = 64 := rfl

lemma baseline_monotone : Monotone2 baseline := by
  simp [baseline, Monotone2]

end PEqualNP.Outside.L_meta_650
