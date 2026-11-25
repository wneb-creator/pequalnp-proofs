# L-meta-6349 shared findings

Assigned2026-11-25T06:09:10Z. Rootrenewalconfirmed06:30:09expiry. Exact mask5805 4by4 representation size10 upper andsize9 exclusion.

2026-11-25T06:24:08.148983+00:00 structural: Plain LRAT Checker replaces the custom trie by BinaryTree (Option Nat); exact inverse token audit passed. The isolated Tree-only check hit the authorized 1000 MB limit after 13.205 s (exit134), no source diagnostics, so it gives no proof verdict. Full source/log/metadata are preserved. Finite Upper then normalization CombinedBridge have the next authorized slots. Rename.lean.txt and RenamePreimage.lean.txt give uncompiled general variable-remapping soundness; child independently confirms720 actual CNF variables and exact literal/sign/order preservation under compact IDs.

2026-11-25T06:26:48.283344+00:00 structural: CheckerRenameProbe.lean PASSED exit0 in8.446s at3072MB cap, peakRSS2923944KiB. This frozen21746B artifact SHA89096007e7f7ad965be2b5cd0171cfae9059738cb339e838a313adeb0e32eff9 contains the full BinaryTree LRAT checker and both generic variable-renaming soundness transfers. Independent checker inverse-token and remapping-source audits passed; complete diagnostic output and metadata preserved beside this note. Root notified for immediate push.

2026-11-25T06:33:19.810665+00:00

## Normalization and canonical SAT lane

Canonical `Link.enc2 8 9` was translated preserving all 13 ordered clause families, row order and literal numbering. The instance has 18,274 clauses, 98,130 literal occurrences, and exactly720 used variables (largest original ID21,373). An independent source/serialization review passed. CaDiCaL returned UNSAT in472.81CPU seconds; its raw ASCII LRAT certificate is1,179,072,387bytes. Toolchain backward slicing retained2,036,244 derived clauses and7,717 original clauses, producing782,544,851bytes. This is solver evidence, not a Lean-checked lower bound; direct packing cannot meet the512KiB PR limit.

`lemmas/CombinedBridge.lean` passed Lean with only Defs and Mathlib.Data.Tree.Basic imports, one worker and4GiB heap cap. The110,087byte artifact includes the BinaryTree-based plain LRAT checker, generic variable-renaming/preimage soundness, the product/And Model/Valid/NF normalization, adjacent independent-gate lexicographic normalization, and Promise.rep_lower44. SHA256358ca2d5d50cb03dc6e70165ca1d30e4c9a171ce8aecd812617e6cdc29f7b884; full log combined-bridge-build-5.log, metadata combined-bridge-result.json. It does not prove the target lower bound. Original declarations were adapted from repository Link.lean, Link2.lean, Promise.lean and the first six Shannon wire-fold declarations; the source transformer is inline_bridge.py.

A dense variable map from the720 used IDs to1..720 and explicit inverse is prepared in VariableMap.lean.txt and compact_variables.py. Its Python bijection/serialization audit passed independently. VariableMapProbe.lean is currently checking inverse correctness on all actual formula occurrences in the Lean kernel. Structural owns unread-primary-input monotonicity; finite is testing whether adding AMO and eight primary-read clauses yields a substantially smaller SAT proof.

VariableMapProbe was cancelled (exit143) after toolchain observed12.2GiB RSS despite-M4096; it has no kernel verdict. Do not describe the concrete map as Lean checked. The generic rename/preimage bridge is checked; the concrete720variable map currently has only an independent exact Python audit.

2026-11-25T06:35:44.554662+00:00 structural: UnreadProbe.lean PASSED exit0 in4.939s, peakRSS2906520KiB. Frozen6491B source SHAa8872df5c777d73a6d0fc0a7d5c74e6b2fe89248fbaa0946548011f2c44c6c21 proves generic unread-input monotonicity and primary_reads_all for the exactmask5805. Direct-primary output exclusion and all16-row goal equality are checked too. This justifies all8 primary-source read clauses without an output-selector exception. Root and finite notified; complete logs/metadata preserved.
