namespace PEqualNP.Outside.L_meta_2602_aux.Normalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Derivative Clamp ClampSemantic

lemma minimum_obstruction (C : Circuit) (hs : C.size ≤ 64)
    (hC : Proper 26 C) (hF : PlaneSpec C) (hZ : MarkedZero C) :
    ∃ D : Circuit, Proper 26 D ∧ PlaneSpec D ∧ MarkedZero D ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, Proper 26 E → PlaneSpec E → MarkedZero E → D.size ≤ E.size) ∧
      AllActive D ∧ 0 < PEqualNP.TopForm.andPairs 26 D ∧
      ∃ j < D.gates.length, (gateAt D j).op = .and ∧ ∃ x : Fin 26 → Bool,
        (D.wires (List.ofFn x)).getD (26 + j) false = true ∧
          D.eval (List.ofFn x) = false := by
  obtain ⟨D, hD, hDF, hDZ, hsize, hmin, hactive⟩ := minimum_all_active C hC hF hZ
  obtain ⟨d, hinit, hd, hz⟩ := hDZ
  have hleft : PEqualNP.Outside.L_meta_2602.directional D 0 13 (d 0) := by
    constructor
    · simpa [markedInitial] using hinit (0 : Fin 2)
    · simpa [DerivativeRules, WireValue, markedBase] using hd (0 : Fin 2)
  have hright : PEqualNP.Outside.L_meta_2602.directional D 13 0 (d 1) := by
    constructor
    · simpa [markedInitial] using hinit (1 : Fin 2)
    · simpa [DerivativeRules, WireValue, markedBase] using hd (1 : Fin 2)
  have shape := PEqualNP.Outside.L_meta_2602.counterexample_shape D
    (hsize.trans hs) hD hDF (d 0) (d 1) hleft hright (hz 0) (hz 1)
  exact ⟨D, hD, hDF, ⟨d, hinit, hd, hz⟩, hsize, hmin, hactive, shape⟩

end PEqualNP.Outside.L_meta_2602_aux.Normalized
