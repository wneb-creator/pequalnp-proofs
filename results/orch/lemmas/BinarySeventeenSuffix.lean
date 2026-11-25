namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation

lemma binaryFloorSeventeen (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨wellFormed, translatedSize, translatedEval⟩ := Signed.toU2_spec C legal
  have small : Signed.HasU2Size pet (C.size - PEqualNP.NotBracket.notCount C) := by
    refine ⟨Signed.toU2 C, wellFormed, translatedSize, ?_⟩
    intro x
    exact (translatedEval x).trans (computes x)
  obtain ⟨D, minimal, budget⟩ := Signed.exists_minU2 small
  obtain ⟨v, s, saved, restricted⟩ :=
    PEqualNP.Outside.L_meta_2592_aux.FirstGate.zero_restriction_saves_two D minimal
  have lower := signedFalseCofactorFloor v s restricted
  omega

lemma excludesThreeNot (C : Circuit) (legal : FanInTwo C)
    (small : C.size ≤ 19) (three : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ¬∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x := by
  intro computes
  have floor := binaryFloorSeventeen C legal computes
  omega

lemma remainingOneOrTwoNot (C : Circuit) (legal : FanInTwo C)
    (small : C.size ≤ 19) (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    1 ≤ PEqualNP.NotBracket.notCount C ∧ PEqualNP.NotBracket.notCount C ≤ 2 := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have floor := binaryFloorSeventeen C legal computes
  obtain ⟨g, member, op⟩ := hasNot
  have present : g ∈ C.gates.filter
      (fun h => @decide (h.op = GateOp.not) (lineDegreeGateOpDecEq h.op GateOp.not)) :=
    List.mem_filter.mpr ⟨member, decide_eq_true op⟩
  have positive : 1 ≤ PEqualNP.NotBracket.notCount C := by
    by_contra! h
    have zero : PEqualNP.NotBracket.notCount C = 0 := by omega
    have empty := List.length_eq_zero_iff.mp zero
    rw [empty] at present
    cases present
  exact ⟨positive, by omega⟩

end PEqualNP.Outside.L_meta_2592
