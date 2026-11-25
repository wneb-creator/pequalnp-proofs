import Mono18RectangleBank

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle

open RectangleRun

def weightTotals : List Int := [79,117,40,231,2439,116,184,137,263,125,135,271,118,111,127,181,1589,440,43]

def weightTotal (w : Nat) : Int :=
  rect (fun r : Fin (rowCount w) => fun c : Fin (colCount w) => weight w r.val c.val)
    Finset.univ Finset.univ

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma weightTotal_valid : ∀ w : Fin 19, weightTotal w.val = weightTotals.getD w.val 0 := by
  intro w; fin_cases w <;> decide +kernel

lemma targetCost_eq (m : Fin 39) : targetCost m.val = weightTotals.getD (matrixWeight m.val) 0 := by
  exact weightTotal_valid ⟨matrixWeight m.val, by fin_cases m <;> decide +kernel⟩

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle
