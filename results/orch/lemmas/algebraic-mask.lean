import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

open PEqualNP.CircuitLowerBounds

def maskedOr : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.or, [2, 1]⟩], 3⟩

lemma maskedOr_isAO2 : PEqualNP.TopForm.IsAO2 2 maskedOr := by decide

lemma maskedOr_tCount :
    PEqualNP.TwoColour.tCount 2 maskedOr (fun i => decide (1 ≤ i)) = 0 := by decide

lemma maskedOr_point :
    PEqualNP.MetaComplexity.circuitFun 2 maskedOr
      (fun i => decide (i = (0 : Fin 2))) = true := by decide

lemma maskedOr_line :
    PEqualNP.MetaComplexity.circuitFun 2 maskedOr
      (fun i => decide (i = (1 : Fin 2))) = true := by decide

end PEqualNP.Outside.L_meta_4675
