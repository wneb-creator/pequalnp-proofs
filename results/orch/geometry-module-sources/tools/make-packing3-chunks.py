import json
from pathlib import Path

p = Path('/tmp/oec/pequalnp-pilot-62')
repo = Path('/workspace/pequalnp-proofs')
counts = json.loads((p / 'packing3-branch-counts.json').read_text())
chunks = []
root_ids = []
for row in counts:
    ids = []
    for start, length, weight in row['groups']:
        ids.append(len(chunks))
        chunks.append((row['root'], start, length))
    root_ids.append(ids)
n = len(chunks)
base = (repo / 'results/orch/lemmas/PackingThreeCheck.lean').read_text()
base = base[:base.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nlemma root_check_21')]
marker = '\nnamespace PackingThree\n\ndef blocks'
glue = (repo / 'results/orch/checked/packing-three-chunk-glue.lean').read_text()
glue = glue[glue.rindex('\nnamespace PackingPrunedDFS\n'):glue.rindex('\nend PEqualNP.Outside.L_meta_1896_aux')]
base = base.replace(marker, '\n' + (p / 'packing3-chunk-definitions.txt').read_text() + glue + marker, 1)
s = f'def chunkData (c : Fin {n}) : Fin 31 × Nat × Nat :=\n  ([' + ', '.join('(' + ', '.join(map(str, triple)) + ')' for triple in chunks) + f'] : List (Fin 31 × Nat × Nat)).getD c.val (0, 0, 0)\n\n'
s += f'def rootChunkIndices (r : Fin 31) : List (Fin {n}) :=\n  (' + str(root_ids) + f' : List (List (Fin {n}))).getD r.val []\n\n'
s += f'''def chunkCheck (c : Fin {n}) : Bool :=
  let r := (chunkData c).1
  PackingPrunedDFS.chunk ok step (PackingPrunedDFS.check ok step good prune 25)
    (rootState r) (rootCandidates r) (chunkData c).2.1 (chunkData c).2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk_coverage : ∀ r : Fin 31,
    ((rootChunkIndices r).flatMap fun c =>
      (List.range (chunkData c).2.2).map fun j => (chunkData c).2.1 + j) =
      List.range (rootCandidates r).length := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk_roots : ∀ r : Fin 31, ∀ c ∈ rootChunkIndices r, (chunkData c).1 = r := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma roots_good : ∀ r : Fin 31, good (rootState r) = true := by
  decide +kernel

'''
defs = base + s
checks = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
for i in range(n):
    checks += f'lemma chunk_check_{i} : chunkCheck {i} = true := by decide +kernel\n\n'
cases = '(fun i => Fin.elim0 i)'
for i in reversed(range(n)):
    cases = f'(Fin.cases chunk_check_{i} {cases})'
checks += f'lemma all_chunks_checked : ∀ c : Fin {n}, chunkCheck c = true := by\n  exact ' + cases + '\n\n'
checks += '''lemma all_rootChecks : ∀ r : Fin 31, rootCheck r = true := by
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

'''
ending = 'end PackingThree\nend PEqualNP.Outside.L_meta_1896_aux\n'
(repo / 'results/orch/lemmas/PackingThreeChunks.lean').write_text(defs + checks + ending)
benchmark = '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk_check_0 : chunkCheck 0 = true := by
  decide +kernel

'''
# Preserve an in-flight benchmark source; generate the glue-enhanced version separately.
(repo / 'results/orch/lemmas/PackingThreeChunkBenchNext.lean').write_text(defs + benchmark + ending)
(p / 'packing3-chunk-data.json').write_text(json.dumps({'chunks': chunks, 'root_chunk_indices': root_ids}))
print('CHUNKS', n, 'SOURCE_BYTES', len((defs+checks+ending).encode()))
