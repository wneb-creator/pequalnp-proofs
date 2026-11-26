import H2ChunkDefs
namespace H2PackedReplay
open PEqualNP.Outside.L_meta_6581
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nodes1540_1667 : blockCheck 1540 128 = true := by
  unfold blockCheck
  apply listPieces_all (d := 5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
end H2PackedReplay
#print axioms H2PackedReplay.nodes1540_1667
