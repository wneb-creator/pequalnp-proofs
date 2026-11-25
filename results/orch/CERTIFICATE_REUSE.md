# Finite-certificate reuse index

Prepared 2026-11-25 for a possible future **leased** finite gap. No new proof work is started. Repository paths are relative to `/workspace/pequalnp-proofs`; `B/` means `/tmp/oec/pequalnp-pilot-178/`.

## Status and entry points

- `results/orch/lemmas/WithdrawnLMeta10760.lean`: frozen 6,037-line, 522,784-byte assembly, SHA256 `50f667bdf48813034b7ded2cc431705ba63b5a488a6da81ff1054e2ad134d5b4`. **Full build and local checker were never run** after the desk withdrew 10760. It is a composition template, not a completed proof.
- `results/orch/assemble-final.py` and `results/orch/assembly-manifest.json`: exact fragment order, source paths and hashes. Do not rerun this graph-specific assembler unchanged.
- `results/orch/lemmas/Lower13.lean`: checked packed-search engine plus 10760 certificate. Full successful logs: `results/orch/lower13-build.txt` and combined named upper 14/lower 13 build `results/orch/build-combined13.txt`.
- `results/orch/lemmas/LratEngine.lean`: checked generic SAT/RUP alternative; full log `results/orch/lrat-engine-build.txt`.
- Archived supplements often import the earlier 10760 module. Strip development imports and copy declarations into the new namespace. The old olean contains a **partial** source, not the frozen full candidate.

## Checked interfaces and preserved tests

All sources in this table start at `results/orch/lemmas/`; logs start at `results/orch/`.

| Source | Interface / meaning | Complete successful log |
|---|---|---|
| `Lower13.lean` | `Sol`, `Live`, `Min`; `look_sound`, `look1_sound`; `Imp E Z L` excludes circuits below L on a restriction; `imp_run` assembles restriction/root checks; `bridge` maps actual fan-in-two circuits to `Sol`. | `lower13-build.txt` |
| `TrackedCore.lean`, `TrackedFull.lean` | `SolCount.live`, `ex_solCount`, `bridgeCount`, `circuit_live_count`: live count t and size k satisfy `t <= notCount C.gates` and `k + (notCount C.gates - t) <= C.size`. | `tracked-core-build.txt`, `tracked-full-build.txt` |
| `OneNotEndpoint.lean` | `live_certificate_false` combines restriction bounds, global minimality and complete mask checks. Its one-NOT wrapper is graph-specific. | `endpoint-build.txt` |
| `ContinuationCut.lean`, `UnaryCoverage.lean` | `chkCut_eq` restores the two root continuations; `lookCut_eq`, `look1Cut_eq` expose one recursive layer; `nots_append` splits unary operands. | `continuation-cut-build.txt`, `unary-coverage-build.txt` |
| `ClosedCoveragePilot.lean` | `patchCut_eq`, `patchBudget_eq`, `chunk_bucket_index_bound`. Exact keys are `(k,t,z,[(s,a,b,c,r),...])`; hashing only selects candidates, with full-key comparison and real-search fallback. Unary root, binary root and parent 0 were computed. | `closed-coverage-build.txt` |
| `AssemblyFromChecks.lean`, `EndpointFromChecks.lean` | Checked restoration and final endpoint **assuming finite checks**; these do not prove all concrete binary leaves. | `assembly-from-checks-build.txt`, `endpoint-from-checks-build.txt` |
| `IndexMask.lean` | `indexMask_mem`, `mem_of_indexMask`: mask equality plus indexbound proves group coverage despite duplicate or unsorted IDs. | `index-mask-build.txt` |
| `LowerZeroChecks.lean`, `Lower13Rest.lean` | All 21 zero-NOT leaves plus original root restoration passed; all remaining t=1..12 checks passed. | `lower-zero-checks-build.txt`, `lower13-rest-build.txt` |
| `FinalBinaryGlue.lean` | All 3,199 IDs covered; three-way group combination checked **conditional on group results**. | `final-binary-glue-build.txt` |

The packed engine is easiest to reuse for the seven-input replacement family copied from accepted `L_meta_10762`. Truth vectors, segment masks, input count, extra input stock and final bridges are graph-specific. Current budget encoding has an explicit `L <= 15` premise; larger budgets need a verified change. The bridge covers repository edge cases, including out-of-range/future reads, empty gates and NOT's first-operand semantics.

## Canonical fragments and dependency order

Use the preserved assembler as authority. All paths here start at `B/`.

1. Before `h0_0`/`iroot`: constants from `proof-route-normalized-init.lean`; then `lrat_route/RootCut.leanfrag`, `PatchCut.leanfrag`, `LookCut.leanfrag`, `BucketCut.leanfrag`; then `certificate_search/StrictNormalize.leanfrag` and **`finite_search/CertificateDataChunked.leanfrag`**.
2. Early lower13 split: `proof_route/LowerZeroSharedData.leanfrag`, `LowerZeroSharedChecks.leanfrag`, `LowerZeroBucketCoverage.leanfrag`, `LowerZeroBucketRoot.leanfrag`, `Lower13Split.leanfrag`.
3. After circuit/NOT bridges: `root_helpers/IndexMask.leanfrag`; `certificate_search/IndexedUnaryFinal.leanfrag`, `BinaryFinalPrefix.leanfrag`; `lrat_route/BucketRows.leanfrag`, `BucketCoverage.leanfrag`; the prelude of `lrat_route/CheckedEndpoint.leanfrag`.
4. Last: `certificate_search/BinaryFinalLanes.leanfrag`, `BinaryFinalAssemble.leanfrag`; `lrat_route/BucketAssemble.leanfrag`; remaining `CheckedEndpoint.leanfrag`; final theorem.

`certificate_search/CertificateData.leanfrag` is the flat predecessor. `BucketCoverageAll.leanfrag` and `BucketCoverageBatched.leanfrag` are abandoned large-batch experiments. The checked recursive `NormalizedLook.lean` wrapper gave no runtime gain and is not in the selected backend.

## Untrusted generation pipeline

All paths start at `B/`. Every export still needs Lean soundness, coverage and leaf checks.

- `certificate_search/engine.py`, `compact-bounds.json`, `generate_lean.py`: corrected executable search, exact restriction order, sampled data and base adaptation.
- `finite_search/trace_unary.py`, `trace_binary.py`, `pack_children.py`: first continuation boundaries and interned W provenance. Then `split_binary.py`, `pack_depth2.py` produce `binary-depth2-packed.json` (42 parents /3,199 leaves for 10760).
- `finite_search/generate_binary_data_compact.py`, `generate_hash_buckets.py`: shared pools and candidate buckets. `chunk_certificate_data.py` converts the corrected flat data into 64-entry `CertificateDataChunked.leanfrag`, preserving flattened contents.
- `certificate_search/final-small-groups.json`: selected 579 groups, seven serial outliers and 286 groups per lane. Earlier greedy 6k/8k plans are experimental.
- Lower13-t0 extraction: `finite_search/trace_lower13_t0.py`, `split_lower13_t0.py`, `pack_lower13.py`; corresponding first/fallback packed JSONs remain there.

Preserve exact Q order, all five W fields, and mode/fuel parameters. Specifically for 10760, mode 0 calls `look1` with K=13/fuel=12; modes 1/2 call `look` with fuel=13. Independently validate transferred restriction truth tables: an early Python self-collision bug invalidated old bounds, which were regenerated. Do not deduplicate sample comparisons: duplicates make positive and negative segment families simultaneously contiguous.

## Resource limits and measured choices

Pinned toolchain: `B/toolchain/lean-4.36.0-linux/bin`; profiler: `B/certificate_search/run_lean_profile.py`. Successful scratch checks used pinned PATH, scratch XDG_CACHE_HOME/MATHLIB_CACHE_DIR, `lake env lean --profile -M 6000`, workdir `/workspace/pequalnp-proofs/lean`, complete stdout/stderr logs. Never `lake update` or rebuild Mathlib.

- Available RAM: 8 GiB/two CPUs; Defs import roughly 2.9 GB. Coordinate **one Lean process**. Site limits read for 10760 were 20 minutes/about 6.5 GB and 512 KiB source; frozen source had only 1,504 bytes spare.
- Monolithic one-NOT checking exceeded memory. Proof-valued definitions serialize expensive `decide +kernel`; theorem bodies may elaborate asynchronously. Use explicit noncomputable data to avoid unnecessary generated code.
- Kernel Arrays are list-backed. Flat 6k batches exceeded 6000 MB; 64-entry chunking passed a6k batch at 37.7s kernel /5,637,064KiB peak. Normalize scalars and **all five W fields including r** using checked `strictSt_eq`/`frcAll_eq`.
- Representative measurements: 519-state leaf 1.18s; all 54 unary leaves 29s; 4,061-state binary leaf 8.59s direct/13.8s compact. Python state counts are poor runtime predictors.
- Same 18 leaves: 28.0s separately versus 35.8s together. Two 3k async checks overlapped at 9.94s/9.07s, peak 4,399,664 KiB. Final plan was seven large checks serially, then exactly two lanes of small groups after all other expensive definitions. **Full final schedule was never measured.**
- Combined 42-parent coverage was stopped after 235.8s near 6.3GB. Keep 42 separate closed checks. Actual closed continuations permit `decide +kernel`; arbitrary-continuation `rfl` normalization was slow.

Detailed measurements and provenance: `results/orch/lemmas/certificate_search.md`, `library_route.md`, and `results/orch/TIMELINE.md`.

## SAT/RUP fallback

`LratEngine.lean` is 2,261 lines/97,228 bytes. `lower_of_certificate` and `lower_of_packed_certificate` accept bounded truth rows and a checked `enc2` UNSAT certificate and prove `s+1 <= C.size` for any fan-in-two circuit computing f. The engine and toy certificate passed; no 10760 UNSAT certificate was obtained.

Generators: `B/finite_search/linkn_enc2.py` matches LinkN2; `B/lrat_route/convert_rup.py` slices/replays RUP and renumbers clauses, rejecting negative/RAT hints. Kernel validation remains mandatory. A 13-gate 128-row trial generated 121MB LRAT without a verdict. Plain `bv_decide`/`bv_check` uses native evaluation here and is unsuitable; use the copied kernel checker. No disallowed Library imports or tactic macros in the final file.

For a newly leased gap: regenerate exact statement/data, prove sample bridge, check restrictions, benchmark a worst leaf, prove exact cut coverage and every leaf, then assemble once and run the full named `lake build`, format guard and `tools/check-lean.mjs`. Python results and conditional smoke tests do not replace those final checks.
