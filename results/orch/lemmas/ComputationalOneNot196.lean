import ComputationalBounds

namespace PEqualNP.Outside.L_meta_10760_aux

def oneQ : List (ℕ × ℕ) := grpSix ++ extendedSeeds

lemma oneQ_sound : ∀ e ∈ oneQ, Imp [] e.1 e.2 :=
  apI grpSix_sound extendedSeeds_sound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneQ_check : chk [] oneQ 0 13 1 FF 1 = false := by decide +kernel

lemma oneQ_pOk : pOk 0 oneQ = true := by decide +kernel

end PEqualNP.Outside.L_meta_10760_aux
