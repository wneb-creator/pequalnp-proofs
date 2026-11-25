import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Among circuits computing the same function, minimize size and then any natural-valued rank. -/
theorem ranked_minimum (n : Nat) (C : Circuit) (mono : Monotone2 C)
    (rank : Circuit → Nat) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n C → D.size ≤ E.size) ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n C →
        E.size = D.size → rank D ≤ rank E) := by
  classical
  let Fits (k : Nat) : Prop := ∃ D : Circuit,
    (Monotone2 D ∧ circuitFun n D = circuitFun n C) ∧ D.size = k
  have existsSize : ∃ k, Fits k := ⟨C.size, C, ⟨mono, rfl⟩, rfl⟩
  obtain ⟨D0, hD0, sizeD0⟩ := Nat.find_spec existsSize
  let Ranked (k : Nat) : Prop := ∃ D : Circuit,
    (Monotone2 D ∧ circuitFun n D = circuitFun n C) ∧
      D.size = Nat.find existsSize ∧ rank D = k
  have existsRank : ∃ k, Ranked k := ⟨rank D0, D0, hD0, sizeD0, rfl⟩
  obtain ⟨D, hD, sizeD, rankD⟩ := Nat.find_spec existsRank
  refine ⟨D, hD.1, hD.2, ?_, ?_⟩
  · intro E hE hfun
    rw [sizeD]
    exact Nat.find_min' existsSize ⟨E, ⟨hE, hfun⟩, rfl⟩
  · intro E hE hfun sizeE
    rw [rankD]
    exact Nat.find_min' existsRank ⟨E, ⟨hE, hfun⟩, sizeE.trans sizeD, rfl⟩

end PEqualNP.Outside.L_meta_1904_aux
