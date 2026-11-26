import RangeAssembly
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8
open PEqualNP.Outside.L_meta_6581
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma c4864 : Replay.DirectMode.Packed.slice 4864 128 = true := by
  unfold Replay.DirectMode.Packed.slice
  apply listPieces_all (d:=5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8
