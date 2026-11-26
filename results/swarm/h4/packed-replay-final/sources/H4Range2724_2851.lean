import PackedDirect

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma h4_2724_2851 : ((List.range' 2724 128).all fun n =>
    Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 n)) = true := by
  apply PEqualNP.Outside.L_meta_6581.listPieces_all (d := 5)
  simp only [PEqualNP.Outside.L_meta_6581.listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay
