import PackedChunkTools
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks
open Replay.DirectMode.Packed
set_option maxRecDepth 32768
set_option maxHeartbeats 0
lemma raw_1248_1279 : (List.range 32).all
    (fun d => checkNode (Fin.ofNat 5230 (1248+d))) = true := by
  apply PEqualNP.Outside.L_meta_6581.listPieces_all (d := 3)
  simp only [PEqualNP.Outside.L_meta_6581.listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
lemma checked_1248_1279 (i : Fin 5230) (lo : 1248 ≤ i.val) (hi : i.val < 1280) :
    checkNode i = true := range_all_sound raw_1248_1279 i lo hi
#print axioms raw_1248_1279
#print axioms checked_1248_1279
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks
