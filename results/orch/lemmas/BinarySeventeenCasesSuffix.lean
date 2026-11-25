namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases
open PEqualNP.Outside.L_meta_2592_aux.Promotion

lemma concreteZeroFloor : ZeroFloor := signedFalseCofactorFloor

lemma signedFirstSourcesNegative (D : Signed.U2Circuit) (legal : Signed.U2Wf D)
    (computes : ∀ x, Signed.u2Eval D x = pet x) (small : D.gates.length ≤ 17)
    (positive : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true ∧
    ∀ j (hj : j < D.gates.length),
      (D.gates[j].a = D.gates[0].a → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].a → D.gates[j].pb = true) ∧
      (D.gates[j].a = D.gates[0].b → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].b → D.gates[j].pb = true) :=
  first_sources_negative_any concreteZeroFloor D legal computes small positive

lemma twoNotSaturation (C : Circuit) (legal : FanInTwo C)
    (small : C.size ≤ 19) (two : PEqualNP.NotBracket.notCount C = 2)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    C.size = 19 ∧ (Signed.toU2 C).gates.length = 17 ∧
      Signed.IsMinU2 pet (Signed.toU2 C) := by
  have floor := binaryFloorSeventeen C legal computes
  obtain ⟨wellFormed, translatedSize, translatedEval⟩ := Signed.toU2_spec C legal
  have translatedComputes : ∀ x, Signed.u2Eval (Signed.toU2 C) x = pet x := by
    intro x
    exact (translatedEval x).trans (computes x)
  have low := binary_floor_of_compute concreteZeroFloor (Signed.toU2 C)
    wellFormed translatedComputes
  have cap : (Signed.toU2 C).gates.length ≤ 17 := by omega
  exact ⟨by omega, by omega,
    minimal_of_cap17 concreteZeroFloor (Signed.toU2 C) wellFormed translatedComputes cap⟩

end PEqualNP.Outside.L_meta_2592
