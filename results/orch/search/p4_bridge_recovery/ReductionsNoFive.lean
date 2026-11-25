import ReductionsBridgeChunks
import ReductionsNormalizeFast

namespace PEqualNP.Outside.Pilot64Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem noFiveOrdered (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, (evalCircuit c r.val).getD 8 false = target r)
    (hl : (derivativeCircuit c 0 1).getD 8 false = false)
    (hd : (derivativeCircuit c 1 0).getD 8 false = false) : False := by
  apply encodedImpossibleChunks c hv
  · intro r
    rw [output_eq_evalCircuit]
    exact hr r
  · rw [derivativeLeft_eq]
    exact hl
  · rw [derivativeRight_eq]
    exact hd

theorem noFiveDistinct (c : Candidate) (hv : distinctFast c)
    (hr : ∀ r : Fin 16, (evalCircuit c r.val).getD 8 false = target r)
    (hl : (derivativeCircuit c 0 1).getD 8 false = false)
    (hd : (derivativeCircuit c 1 0).getD 8 false = false) : False := by
  apply noFiveOrdered (normalizeFast c) (normalizeFast_valid c hv)
  · intro r
    rw [evalCircuit_normalizeFast]
    exact hr r
  · rw [derivativeCircuit_normalizeFast]
    exact hl
  · rw [derivativeCircuit_normalizeFast]
    exact hd

end PEqualNP.Outside.Pilot64Bridge
