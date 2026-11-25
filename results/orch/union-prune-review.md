# Independent review of finite union/pruning helper

Verdict: PASS for preservation as a checked supporting artifact; this is not a proof or refutation of L-meta-2592.

Reviewed UTC: 2026-11-25T14:38:34.318532+00:00
Source: `results/orch/lemmas/union_prune_all_chunks.lean`
SHA256: `953da8fd112cb367155e2c98d23af94a7ed60d40edd690cb9a93ee1c663177e1`
Size: 240,513 bytes; 7,202 lines.

The exact conclusion is `PEqualNP.Outside.L_meta_2592.starHelperSearch = false`. The file enumerates the 53 nonzero, nonsingleton six-bit masks excluding the four target masks. Their list exactly matches the filter in `helperMasks_spec`. Target masks 22, 37, 25, 42 represent bce, acf, ade, bdf with a through f in increasing bit positions.

The search checks all 23,426 unordered triples of distinct helpers. I independently parsed and checked every one of the 1,378 pair declaration names against its stated arguments and `decide +kernel` body; every row refers exactly to all larger second helpers; the final assembly refers to all 53 rows. Declaration names are unique. No candidate helper name conflicts with the current named proof file.

`setStepAllowed` permits a target subset of an existing set, or the union of two existing sets. The subset test has the intended direction. `closeStarStep` only adds a previously absent member of the seven allowed masks; it never removes a known mask. Consequently the length-based early stop detects no additions, and seven full passes are sufficient to reach closure. These observations explain the finite algorithm; they are not the missing general Lean semantic lemmas.

The file uses only its initial Mathlib import, one permitted helper namespace, definitions/lemmas, and local maxRecDepth/maxHeartbeats limits. There are no forbidden root identifiers, strings, attributes, holes, extra axioms, native evaluation, metaprogramming commands, or unapproved options. Its byte size is below the 512 KiB submission limit. The standalone helper has no final named gap theorem and is therefore not a complete submission file.

Validation record `results/orch/union-prune-all-validation.txt` reports Lean exit 0 for this exact source hash. Full existing stdout/stderr are retained in the paths named there. I did not rerun Lean or the repository checker. The checker failure recorded elsewhere is not upgraded by this helper's successful compilation.

Two bridges remain explicitly unproved: a general seven-operation set program must map into this closure, and an arbitrary one-NOT circuit must map into the proposed set-program model. The certificate must not be described as a 20-gate lower bound until the required bridges and exact posted theorem are proved.
