import H5BlockSupport
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma range3264 : block 3264 64 := by
  apply block_add (left := 32) (right := 32)
  all_goals apply block_add (left := 16) (right := 16)
  all_goals apply block_add (left := 8) (right := 8)
  all_goals apply block_add (left := 4) (right := 4)
  all_goals unfold block
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
