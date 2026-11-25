import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.ProvenanceCounterexample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shielded : Circuit :=
  ⟨[⟨GateOp.and, [0,0]⟩, ⟨GateOp.or, [2,1]⟩], 3⟩

def exposed : Circuit :=
  ⟨[⟨GateOp.and, [0,0]⟩, ⟨GateOp.or, [0,1]⟩], 3⟩

lemma same_semantics_different_tCount :
    circuitFun 2 shielded = circuitFun 2 exposed ∧
      PEqualNP.TwoColour.tCount 2 shielded (fun i => decide (1 ≤ i)) = 0 ∧
      PEqualNP.TwoColour.tCount 2 exposed (fun i => decide (1 ≤ i)) = 1 := by
  decide

lemma equal_signals_different_orIn :
    (fun x : Fin 2 → Bool => (shielded.wires (List.ofFn x)).getD 2 false) =
      (fun x : Fin 2 → Bool => (shielded.wires (List.ofFn x)).getD 0 false) ∧
      PEqualNP.TopForm.orIn 2 shielded 2 = ∅ ∧
      PEqualNP.TopForm.orIn 2 shielded 0 = {0} := by
  decide

end PEqualNP.Outside.L_meta_4970_aux.ProvenanceCounterexample
