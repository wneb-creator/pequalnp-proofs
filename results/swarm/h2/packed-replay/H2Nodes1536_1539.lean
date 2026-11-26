import H2ChunkDefs
namespace H2PackedReplay
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nodes1536_1539 : blockCheck 1536 4 = true := by
  decide +kernel
end H2PackedReplay
#print axioms H2PackedReplay.nodes1536_1539
