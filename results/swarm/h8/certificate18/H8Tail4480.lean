import RangeAssembly
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail
open PEqualNP.Outside.L_meta_6581
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma c4480 : Replay.DirectMode.Packed.slice 4480 128 = true := by
  unfold Replay.DirectMode.Packed.slice
  apply listPieces_all (d:=6)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail
