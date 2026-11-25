import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux

def upperCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [1, 10]⟩,
    ⟨.or, [3, 7]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 14]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [5, 16]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [5, 18]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [17, 22]⟩,
    ⟨.or, [20, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_670_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_670_upper :
    PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨PEqualNP.Outside.L_meta_670_aux.upperCircuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo,
      PEqualNP.Outside.L_meta_670_aux.upperCircuit]
  · decide +kernel
