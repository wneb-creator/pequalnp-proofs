# Independent review of merged partial

Reviewed at 2026-11-25 09:56 UTC by constructive_search.

File: lean/PEqualNP/Outside/L_meta_1479.lean
Lines: 838. Bytes: 36,553.
SHA256: 1371c69f728b13b9b8174da0555be477c7e80eaea1a57c1baeece27cfec57740

Verdict: PASS for a clearly labeled partial archival push, conditional on the root's current named build succeeding. This is NOT a proof of the posted size27 statement and is NOT ready for the proof PR.

I read all838 lines independently. The complete target theorem is absent. relaxed_28 is exactly the posted statement with only C.size≤27 replaced by C.size≤28; its witness has28 gates. baseline_size proves27 only for the ordinary star circuit and no double re-read claim is attached to that baseline.

Finite boundary certificate:
- Independently parsed the literal masks from the Lean source and enumerated all16,384 inputs.
- The positive list contains exactly the21 distinct incidence pairs.
- The negative list contains exactly the37 distinct maximal independent assignments, with no omissions or extras.
- positiveMasks_cover proves the positive minimal rows represent every incidence.
- negativeMasks_cover ranges over every7-bit point assignment; its selected row contains those points and all lines not adjacent to them. This is sufficient to dominate every false full input. boundary_correct then correctly applies circuit monotonicity in both directions.
- positiveMasks_valid and negativeMasks_valid certify that the finite test rows themselves have the intended truth values.

Other mathematical checks:
- BinaryAO matches the desk's backward, distinct binary AND/OR shape.
- DerivativeTrace is the exact Boolean product-rule recurrence. Existence and dark-AND zero proofs are well-founded and preserve the required base/seed roles.
- derivative_support_of_bounds uses simultaneous wire-value and trace induction, with valid backward-wire bounds; derivative_false_of_pair_false follows correctly. No deletion/replacement claim beyond that lemma is present.
- Strict Hall and the seven-vertex-cover rigidity proof are correctly scoped to vertex covers, not claimed as circuit lower bounds.
- Final-AND singleton-support thinness uses monotonicity, singleton disjointness and the finite no-four-cycle property correctly.

Format and integrity checks:
- All65 declarations are unique and inside the file-owned namespace.
- Only the allowed project module and Mathlib modules occur on the initial import lines.
- No forbidden marker, string literal, command marker, attribute, admission, new axiom, native/bv decision tactic, or credential-pattern match.
- File is regular UTF-8, not executable, not a symlink, well below512KiB. Current mode0600 is acceptable; git records the regular-file mode100644.
- Because the final target theorem is absent, the outside guard's no-theorem rejection is expected for this partial archive.
