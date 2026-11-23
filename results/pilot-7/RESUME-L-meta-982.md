# L-meta-982 preserved partial work

KIT-MESSAGE-ID msg-b493ff75057293776fcb9f22

Work stopped on 2026-11-23 after desk renewal returned HTTP410: the lease expired. The required identical diagnostic retry also returned410. Do not reuse this lease or assume the gap is assigned. No upstream PR was opened; the exact 31-conjunct theorem remains unproved in Lean.

## What is checked

- Repository target `lean/PEqualNP/Outside/L_meta_982.lean` contains only a component proof. `lake build PEqualNP.Outside.L_meta_982` passed (18363 jobs); this does not establish the full posted statement.
- `Structural982Minimal.lean` proves 15 posted conjuncts directly and cases17/21 conditionally on seed0.
- `Seed0Lower982.lean` and `C7Lower982.lean` separately prove the exact unconditional bounds for cases0/8. Their complete finite tables, symmetry checks, semantic bridges, compiler output and independent audits are preserved. The common declarations must be deduplicated if combining the modules.
- Generic circuit normalization, upper-budget finite-checker soundness, exact semantic bridges, optimized scores/coverage, compressed state reconstruction and symmetry transport are compiled in separate modules. See their manifests and audits for scope.
- All31 cases have complete independent search datasets, preserved in `search-data-982.tar.gz`. These are untrusted certificate data; they are not a substitute for the remaining kernel closure checks.

## Most promising continuation

Use the finite-only implementation to fit the512KiB single-file limit. The latest radix Huffman state tables use324397 bytes for all31 cores and79270 stored states. `Huffman982AllStateWrappersCheck.lean` elaborates all wrappers and proves four sampled state equalities; it does not prove closure. Independent audits check all records and numeric data.

The bit-sliced encoding packs score witnesses into arithmetic bitplanes (`SliceOpt982`, `OldCoverage982`). The same challenging core28 leaf compiled in30.033 seconds with OldCoverage; a full compressed-table closure has not yet been measured. Generic paired replay (`PairReplay982`) transports images by replaying the same gates, avoiding repeated coordinate permutation per word. `GroupedSymmetry` merges displacement masks. `CoordinateSymmetry` derives coordinate permutations from encoded assignment rows and small vertex permutations, avoiding large literal coordinate maps. The exact arbitrary-word checks still validate each constructed generator.

Remaining work includes wiring paired replay to the compressed tables, verifying all remaining closures within runtime limits, deriving the semantic row bridge from encoded input columns to save source space, and assembling exactly the posted statement in `statement-982.txt`. Some original proofs contain names with the banned substring `_root_`; final assembly must rename them. Scratch modules use imports and global options unsuitable for final submission; flatten dependencies and scope the permitted limits.

## Reproduction and submission limits

All retained source and full diagnostics are under this directory. Search data archives include the generation scripts and encoded tables. Scratch imports assume these modules are copied to a single directory and compiled in dependency order with the pinned Lean toolchain. `c7_run_lean.py` is the bounded compiler runner. The previous container used a warm Mathlib cache and did not build Mathlib from source.

A final PR must add exactly one file, `lean/PEqualNP/Outside/L_meta_982.lean`, with imports only Mathlib and PEqualNP.Defs, no sorry/new axioms/native_decide, no string literals, no banned root substring, and only the allowed attributes/options. The user specified a clean single-file PR branch built by the Mac; the checkpoint branch retains results. Do not submit this multi-file checkpoint branch as a completed proof PR.

The full repository local checker has not accepted this gap. No cleanup pass was claimed. Use `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_982.lean <exact-statement-file> check` only on a complete candidate, and preserve its complete output. No further desk request was made after the expired-lease error.
