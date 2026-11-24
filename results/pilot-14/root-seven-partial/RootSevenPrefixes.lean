import RootSevenCounts
namespace PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prefixes_checked : ∀ i : Fin 12, ∀ j : Fin 3, prefixCheck i.val (j.val+6) = true := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

lemma prefixes_excluded (i : Fin 12) (j : Fin 3) :
    LiveCheck.Impossible 11 (child i.val (j.val+6)).nots (child i.val (j.val+6)).wires :=
  prefixCheck_sound i.val (j.val+6) (prefixes_checked i j)
end PEqualNP.Outside.L_meta_670_aux.RootSevenLeaf
