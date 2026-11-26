import H2ChunkDefs
namespace H2PackedReplay
open PEqualNP.Outside.L_meta_6581
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma tail1924_2051 : blockCheck 1924 128 = true := by
  unfold blockCheck
  apply listPieces_all (d := 5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
end H2PackedReplay
#print axioms H2PackedReplay.tail1924_2051
