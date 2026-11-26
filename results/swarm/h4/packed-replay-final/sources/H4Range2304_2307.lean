import PackedDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma h4_2304_2307 : ((List.range' 2304 4).all fun n =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 n)) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay
