# Independent preservation audit at the first L1884 checkpoint

UTC: 2026-11-25T15:56:53.888210+00:00
Verdict: PASS for the fixed listed snapshot, with checked helpers, drafts, and unsuccessful searches distinguished. No full proof/refutation of L-meta-1884 or checker acceptance is claimed.

PRESERVATION-MANIFEST-1555.json records 225 stable files, 7117251 total bytes, their hashes, and scan results at 2026-11-25T15:56:29.850828+00:00. This is a fixed snapshot, not a promise about files subsequently edited. Its own file and this report are outside the manifest. The two actively written stochastic logs semantic.stdout/.stderr were excluded; the complete-prefix semantic-audit-snapshot copies and audit-status record are included. No file changed while being read.

No credential-pattern finding, sensitive credential JSON key, invalid JSON, symlink/nonregular-file issue, or unexpected nontext content was found. The three nontext files are generated Lean objects ReaderBound.olean, Unary18Check.olean, and NineCircuitFloor.olean. Their hashes establish dependency provenance; source and logs suffice for branch preservation, and these generated binaries need not be committed. Both gzip archives decompress to valid JSON and contain 3172 + 92 = 3264 complete diagnostic records. Compressed and decompressed content was scanned without printing any possible secret values.

## Proof status

InputEssentiality, KWFormula, KWTarget, SoleOrPartner, PairLocalization, and ThreeBlockers are individually checked Defs-only helpers with independent semantic reviews. Unary17Check, LiveDirectional, MonoExtensionCheck, Unary18Check, and NineCircuitFloor are checked dependency tests whose imports must be replaced by in-file definitions in any final single-file submission. MonoBase is now separately checked; its source matches its earlier preserved copy exactly. ReaderBound is checked and has a separate review by lean_setup, with its cofactor lower-bound hypothesis explicitly retained. The named InputEssentiality + KWFormula + PairLocalization partial assembly has its own exact-content review; any later named assembly needs a new matching build and hash review.

Unary17Standalone and the full Mono18 standalone assembly are not yet established by the dependency tests. Unary18Conditional's latest exact text was not rerun after the final fixes; it is a development artifact. KW.lean, KWSmall.lean, and KWBound.lean are explicitly identified as failed/uncompiled drafts in KW-ATTEMPTS.md, with diagnostic history preserved. They are not represented as proofs. This audit does not retroactively validate those drafts.

## Search status and provenance

The frozen SAT CHECKPOINT_STATUS inventory verifies all 85 listed file hashes exactly. All three global target searches are UNKNOWN. The 816 UNSAT local repairs pin fifteen of eighteen gate definitions and exclude only those three-gate neighborhoods; they do not prove a global circuit lower bound. Positive baseline tests use twenty/twenty-one gates, and the cofactor auxiliary positive validation uses twenty-four gates. None is an eighteen-gate counterexample. Full assignment validation is recorded for each actual positive encoder test.

The stochastic archive explicitly says no exact witness was found. Compressed-row best scores are accompanied by full-cube validation reports; incomplete scores are not labelled proofs. search_cegis.cpp is a prepared variant, not a completed target search. Its separate positive/hidden-error self-test only validates detection of an omitted row. The active semantic solver is represented by a timestamped prefix snapshot.

The public matching evidence reports no exact posted target matching our new partials, and correctly excludes the already checked L1507 negated twin as a new submission opportunity. Research notes and source generators are preserved separately from checked result claims. No desk call, lease change, git mutation, or new search was performed by this audit.

Update 2026-11-25T15:59:48.088350+00:00: a later standalone-format audit found two global options without `in` in the checked ReaderBound helper. They violate CONTRIBUTING.md62–64 despite being permitted option names. This does not change mathematical compilation status or prevent labelled draft preservation, but it blocks a final-format claim until corrected and rechecked. See REVIEW-reader-standalone.md.

Update 2026-11-25T16:03:11.862365+00:00: the ReaderBound format finding is resolved in source252337b… by removing only the two global limits and recompiling the helper successfully. Regenerated ReaderStandalone58addd4… passes assembly/format review but remains unbuilt. The original manifest intentionally continues to record the older snapshot hashes.
