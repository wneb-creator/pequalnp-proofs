import H4Aggregate2304_2595
import H4Range2596_2723
import H4Range2724_2851

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay

lemma checked_2304_2851 (i : Fin 5230) (lower : 2304 ≤ i.val) (upper : i.val ≤ 2851) :
    Replay.DirectMode.Packed.checkNode i = true := by
  by_cases first : i.val ≤ 2595
  · exact checked_2304_2595 i lower first
  · by_cases second : i.val ≤ 2723
    · exact range_checked h4_2596_2723 i (by omega) (by omega)
    · exact range_checked h4_2724_2851 i (by omega) (by omega)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay
