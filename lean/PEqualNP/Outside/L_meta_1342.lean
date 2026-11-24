import PEqualNP.Defs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_1342

open PEqualNP.CircuitLowerBounds

def baselineCircuit : Circuit :=
  ⟨[
    ⟨.or, [9, 10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [15, 10]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [5, 18]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [20, 10]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.and, [8, 25]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [27, 17]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.or, [29, 22]⟩,
    ⟨.or, [30, 24]⟩,
    ⟨.or, [31, 26]⟩], 32⟩

lemma baseline_monotone : PEqualNP.MetaComplexity.Monotone2 baselineCircuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, baselineCircuit]

lemma baseline_size : baselineCircuit.size = 22 := rfl

end PEqualNP.Outside.L_meta_1342
