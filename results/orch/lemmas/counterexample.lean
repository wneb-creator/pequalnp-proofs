import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds

def auditC : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 3]⟩, ⟨.or, [4, 4]⟩], 5⟩

lemma audit_isAO2 : PEqualNP.TopForm.IsAO2 3 auditC := by
  decide +kernel

lemma audit_tCount :
    PEqualNP.TwoColour.tCount 3 auditC (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma audit_star_function : ∀ x : Fin 3 → Bool,
    (auditC.wires (List.ofFn x)).getD 5 false = (x 1 || x 2) := by
  decide +kernel

lemma audit_or_reach_empty : PEqualNP.TopForm.orIn 3 auditC 5 = ∅ := by
  decide +kernel

end PEqualNP.Outside.L_meta_4970_aux
