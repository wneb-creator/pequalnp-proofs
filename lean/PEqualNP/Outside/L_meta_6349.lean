import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349

def upperCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[
    ⟨.or, [1, 6]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [11, 14]⟩,
    ⟨.or, [15, 16]⟩
  ], 17⟩

lemma upperBound :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨upperCircuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, upperCircuit]
  · decide
  · decide

end PEqualNP.Outside.L_meta_6349
