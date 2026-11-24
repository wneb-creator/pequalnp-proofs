import RootSevenCounts
namespace PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma children0_checked : ∀ i : Fin 12, check i.val 0 = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma children0_excluded (i : Fin 12) :
    LiveCheck.Impossible 11 (child i.val 0).nots (child i.val 0).wires :=
  check_sound i.val 0 (children0_checked i)
end PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
