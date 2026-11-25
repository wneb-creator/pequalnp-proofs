import PackingThreeDefs
import PackingChunkProofs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingThree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma assemble_checks
    (chunk_coverage : ∀ r : Fin 31,
      ((rootChunkIndices r).flatMap fun c =>
        (List.range (chunkData c).2.2).map fun j => (chunkData c).2.1 + j) =
        List.range (rootCandidates r).length)
    (chunk_roots : ∀ r : Fin 31, ∀ c ∈ rootChunkIndices r, (chunkData c).1 = r)
    (roots_good : ∀ r : Fin 31, good (rootState r) = true)
    (all_chunks_checked : ∀ c : Fin 236, chunkCheck c = true) :
    ∀ r : Fin 31, rootCheck r = true := by
  intro r
  have hb : PackingPrunedDFS.branches ok step
      (PackingPrunedDFS.check ok step good prune 25)
      (rootState r) (rootCandidates r) = true := by
    apply PackingPrunedDFS.branches_of_branchAt
    intro i hi
    have hm : i ∈ ((rootChunkIndices r).flatMap fun c =>
        (List.range (chunkData c).2.2).map fun j => (chunkData c).2.1 + j) := by
      rw [chunk_coverage]
      exact List.mem_range.mpr hi
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp hm
    obtain ⟨j, hmem, heq⟩ := List.mem_map.mp hj
    have hcheck : PackingPrunedDFS.chunk ok step
        (PackingPrunedDFS.check ok step good prune 25)
        (rootState r) (rootCandidates r) (chunkData c).2.1 (chunkData c).2.2 = true := by
      have h := all_chunks_checked c
      simpa only [chunkCheck, chunk_roots r c hc] using h
    have h := PackingPrunedDFS.branchAt_of_chunk ok step
      (PackingPrunedDFS.check ok step good prune 25)
      (rootState r) (rootCandidates r) (chunkData c).2.1 (chunkData c).2.2 j
      hcheck (List.mem_range.mp hmem)
    simpa only [heq] using h
  unfold rootCheck
  rw [PackingPrunedDFS.check, roots_good r, hb]
  simp

end PEqualNP.Outside.L_meta_1896_aux.PackingThree
