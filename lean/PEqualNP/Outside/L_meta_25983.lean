import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25983 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.NotBracket.notCount C ≤ 1 ∧
      PEqualNP.Represents.Represents
        (fun (u : Fin 4) (v : Fin 4) =>
          (([12, 7, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [14, 15]⟩], 16⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
