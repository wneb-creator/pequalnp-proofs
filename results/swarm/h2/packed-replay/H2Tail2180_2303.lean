import H2ChunkDefs
namespace H2PackedReplay
open PEqualNP.Outside.L_meta_6581
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tail2180_2303 : blockCheck 2180 124 = true := by
  unfold blockCheck
  apply listPieces_all (d := 5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
end H2PackedReplay
#print axioms H2PackedReplay.tail2180_2303
