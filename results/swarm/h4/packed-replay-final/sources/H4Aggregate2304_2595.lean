import H4Aggregate2304_2339
import H4Range2340_2467
import H4Range2468_2595

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay

lemma checked_2304_2595 (i : Fin 5230) (lower : 2304 ≤ i.val) (upper : i.val ≤ 2595) :
    Replay.DirectMode.Packed.checkNode i = true := by
  by_cases first : i.val ≤ 2339
  · exact checked_2304_2339 i lower first
  · by_cases second : i.val ≤ 2467
    · exact range_checked h4_2340_2467 i (by omega) (by omega)
    · exact range_checked h4_2468_2595 i (by omega) (by omega)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay
