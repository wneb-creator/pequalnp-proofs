import H2IntervalBridge
import H2Extra2852_2961
import H2Extra2962_3071
namespace H2PackedReplay
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
lemma extra_checked (i : Fin 5230) (hlo : 2852 ≤ i.val) (hhi : i.val < 3072) :
    checkNode i = true := by
  by_cases h : i.val < 2962
  · exact check_interval 2852 110 extra2852_2961 i hlo (by omega)
  exact check_interval 2962 110 extra2962_3071 i (by omega) hhi
end H2PackedReplay
#print axioms H2PackedReplay.extra_checked
