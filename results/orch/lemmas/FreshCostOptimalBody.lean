import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

lemma replacement_optimal (T : PEqualNP.CircuitLowerBounds.Circuit)
    (hT : PEqualNP.TopForm.IsAO2 8 T)
    (hf : PEqualNP.MetaComplexity.circuitFun 8 T =
      PEqualNP.MetaComplexity.circuitFun 8 C) : D.size ≤ T.size := by
  have hTf : ∀ z : Fin 8 → Bool,
      PEqualNP.MetaComplexity.circuitFun 8 T z =
        decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
          z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
    intro z
    rw [hf]
    exact computes_C z
  have hbound := PEqualNP.Outside.L_meta_2585.Support.incident_vertices_card_le
    2 6 I T hT hTf
  have hcard : (Finset.univ.filter (fun v : Fin (2 + 6) =>
      ∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        (v = Fin.castAdd 6 p ∨ v = Fin.natAdd 2 l))).card = 8 := by decide
  rw [hcard] at hbound
  change 7 ≤ T.size
  omega

lemma optimum_plus_repeats_too_large :
    C.size < D.size + (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample
