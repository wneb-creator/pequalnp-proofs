# Preserved finite-search data

Job: pequalnp-pilot-134. Gap: L-meta-1890.

These are independently audited exploratory checkpoints, not Lean proofs. Every recorded search was interrupted at its time limit without closure or a target circuit. No full proof or refutation is claimed.

## Current checkpoints

| Checkpoint | Closed states | Scope |
| --- | ---: | --- |
| live-seed-nots3-v2-closed.pkl.gz | 9,391 | Seeded; at most 3 NOTs; initial audited run |
| live-plain-nots2-v2-closed.pkl.gz | 8,157 | Seed unused; at most 2 NOTs |
| live-seed-nots3-width-v2-closed.pkl.gz | 17,765 | Seeded; at most 3 NOTs; width cuts; supersedes the first row |
| live-seed-unbounded-width-v2-closed.pkl.gz | 10,125 | Seeded; no global NOT bound; width cuts |

The third checkpoint contains every closed state in the first. The latest seeded explicit-budget checkpoint, the unseeded checkpoint, and the width-only checkpoint are distinct search modes. Resume only with an exactly matching mode tuple. The tuple fields are version, clipped seed, seed live, initial gate cap, nine-vertex lower bound, symmetry, and maximum NOT count. The version is `budget-siblings-v2`.

Only completed states are saved: active recursion ancestors are excluded. Checkpoint state keys contain the remaining gate budget, remaining NOT budget (or None), and canonical sorted live truth tables. Archive validation checked the tuple/version, state shape, proper and distinct 1024-row wires, width bound, absence of the target among closed-state wires, and agreement with each complete log's final summary. A data-only unpickler rejecting all globals was used for this metadata inspection.

## Audit and proof status

Independent agent `/root/finite_certificate/search_audit` reviewed NOT-sensitive sibling/memo/checkpoint keys, automorphisms, explicit four-row chain witnesses, target handling, and restricted-prefix DAG pruning. Python independently checks each chain witness has outputs true,false,true,false and ordered live-wire coordinates. C cover and chain detectors were cross-checked against separate Python implementations; complete validation output is included.

The 3/2-NOT modes rely on the separate checked Petersen non-NOT lower bound L-meta-6581 and still need formal linkage from original circuits to the extracted plan's NOT count. The width-only mode uses only the live-width bound. All modes use checked smaller-graph/nine-vertex bounds as mathematical inputs; the full generator, graph transports, and exhaustive search have not been certified in Lean. Current Lean drafts and their actual validation status remain in the parent finite directory.

## Invalid earlier checkpoints

Do not resume `live-seed-nots3-closed.pkl.gz` or `live-plain-nots2-closed.pkl.gz`. They predate the fix that includes postmove NOT cost in sibling deduplication; a NOT and binary move reaching identical wires could incorrectly share an exclusion. Those two checkpoints were deliberately not copied. Their complete logs are retained as `live-search-seed-nots3.txt` and `live-search-plain-nots2.txt`, for historical diagnosis only.

The old unversioned smoke checkpoints `live-checkpoint-smoke.pkl.gz` and `live-checkpoint-smoke2.pkl.gz` were also omitted; they are not production resume artifacts. The old hypothetical target-handling issue is fixed in v2: finding a target raises immediately, preventing its ancestors entering the closed set. No target was observed in any retained log.

## Contents

The four complete final search logs are preserved byte for byte beside their checkpoints. The additional chain-certificate JSON/log contains ten sampled, independently witnessed cuts, not Lean-certified branch exclusions. Compressed checkpoints are data files; no executables, shared libraries, oleans, build caches, or credentials are included. `manifest.json` records final summaries, byte sizes, SHA256 hashes, and current generator source hashes. Original compression is preserved.
