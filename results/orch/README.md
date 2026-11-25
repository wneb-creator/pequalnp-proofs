# Pilot 98 preserved work

Final status: stopped under the shared-handle rule; see FINAL-DESK-STOP.md and validation.txt. No complete proof or refutation.

Current work moved to L-meta-2583 at 2026-11-25 14:42:44 UTC after the L-meta-2592 lease returned HTTP 410. The earlier result and full diagnostic are preserved in this branch. No posted statement has been proved or refuted and no proof PR has been opened.

## L-meta-2583

The named file currently has 3,507 lines and only imports PEqualNP.Defs. Its named `lake build` passes. It proves the sharp upper and lower bounds for read-one incidence circuits, a plane perfect matching, and an exact equivalence between the requested normalization and the unrestricted gate lower bound. It does not prove the unrestricted bound or declare the final posted theorem. An independent reviewer checked the source and provenance.

The unmodified checker against the exact posted statement was killed with exit 137 before a verdict. See `2583-checker-01.log` and `2583-checker-01-status.txt`. This is not checker acceptance. The normal build log is `2583-build-03.log`; `.raw.gz` preserves its original bytes.

The order-three circuit searches and their controls are in `2583-search/` and `2583-exact/`. Failed searches are not lower-bound certificates. The exact Boolean test boundary (52 minimal true and 704 maximal false assignments) has been independently recomputed, including all 8,192 point subsets.

The notes below describe the earlier L-meta-2592 checkpoint.

---

# L-meta-2592 partial research checkpoint

The posted circuit lower bound is NOT proved or refuted. No proof PR is opened.

The named Lean file builds and contains supporting graph facts, a20-gate witness, an18-gate approximation with its exact four-error formula, and restricted input-NOT lemmas. The complete finite union/pruning certificate in lemmas/union_prune_all_chunks.lean also compiled, as recorded in its validation and independent review. This is only a finite helper result; both semantic bridges remain absent.

Checkpoints01–06 preserve successful builds and reviews. validation.txt gives current status; checkpoint-05/checker.txt preserves the unmodified checker fault. Search directories preserve complete selected logs and compact reproducible sources; UNKNOWN/heuristic failures are not lower bounds.

Other Lean variants are research drafts unless a matching successful validation file is present. In particular signed_paths.lean is uncompiled after a memory-limit failure, and union_prune_bridge.lean was canceled after lease loss.

All work stopped after the desk returnedHTTP410. The root heartbeat timer was stopped before preservation. No other pilot lease was released.

Readable diagnostic copies normalize line endings and trailing whitespace. Matching .raw.gz files preserve the original complete bytes.
