# Certificate route for L-meta-10760

2026-11-25 19:07 UTC: generated an unverified Lean candidate proving the stronger partial result that every AND/OR/NOT fan-in-two circuit for the target function needs at least 13 gates. The candidate is `/tmp/oec/pequalnp-pilot-178/certificate_search/Lower13.lean`, 3787 lines / 223078 bytes, with only `PEqualNP.Defs` imported and all helpers in the required namespace. It copies the generic soundness engine from accepted L_meta_10762, regenerates graph-specific truth vectors and pair-segment constants, and checks 45 induced-graph lower bounds before the root bound. Every numeral is at most 18 decimal digits (larger constants use transparent limb folds). It still needs Lean compilation; no acceptance is claimed.

The final monotone circuit upper bound found by the other route is currently 14, so the target proof remains open. A corrected Python port of the exact computational checker validates the lower-13 certificate in roughly 5 seconds. A lower-14 check timed out at 50,000 states / 13 seconds; no conclusion about 14 was obtained.

Generated sample construction: all 64 assignments of weight at least four occupy the low 64 truth bits; each true edge is paired with all maximal false assignments and its own false subsets; each true triple is paired with contained maximal false assignments. The resulting 189 pairs are duplicated, grouped once by positive row and once by negative row, giving NN=500, 41 positive segments, and 17 negative segments. The kernel lemma EF_ok verifies the sample target matches the graph function.

Important validation correction: an initial Python port incorrectly included self-loops in its bipartiteness calculation. This overstated some restriction lower bounds. The bug was fixed before producing Lower13.lean, and all restriction tables were regenerated from scratch. The corrected single-variable-zero bounds are 10 for variables 0 through 5 and 9 for variable 6. Corrected double-variable-zero bounds are 7 except masks 12,68,72, which have bound 6. The proof_route agent independently matched these against accepted subinstance certificates. All original erroneous bounds and test14 runs using them are discarded.

Explicit small-instance sanity checks: deleting variable 0 admits a 10-gate circuit with expression `(x3 OR x5) AND (x1 OR x6) OR x4 AND (x1 OR x2) OR x2 AND x6 OR x3 AND x5`; deleting variables 2 and 3 admits the six-gate circuit `(x0 OR x1) AND (x4 OR x5) OR x6 AND (x0 OR x5)`. The corrected checker permits these sizes.

Scratch artifacts: engine.py, generate_lean.py, data.json, compact-bounds.json, compact.log, search-bounds-fixed.log. No tracked proof file was changed by this agent. No desk calls or git writes were performed. Expensive searches are paused at root request while dependencies build.

2026-11-25 19:11:12 UTC: Lower13.lean compiled successfully with pinned Lean 4.36.0, exit 0, in about 2 minutes 42 seconds. Full compiler output is in `certificate_search/lower13-build.log`; it contains inherited deprecation/linter warnings, no errors. The lower bound 13 is now kernel checked.

2026-11-25 19:12 UTC: corrected Python checker also returned false for the specific case `chk [] (pr ac4 0) 0 13 1 FF 1`, after 350852 states / 24.04 seconds. This excludes a 13-gate live circuit using exactly one NOT, subject to Lean validation. No lower-14 check for zero-NOT circuits is needed: the main proof can reuse a zero-NOT input circuit directly. For an input with one NOT and at most 13 gates, the lower-13 result forces any tracked live extraction to retain all 13 gates and its one NOT. Agent gate_elimination is formalizing this tracked extraction.

The local theorem variant is prepared in `OneNotBoundStep.lean`: `live_certificate_false` accepts a live circuit with a fixed NOT count, plus global minimality and the one-count checker result. Its `oneNotLiveImpossible` wrapper expects live length 13 / NOT count 1, initial subset `C (mz 0) (WZ [] 0)`, and the computational equality above. Scratch import harnesses `OneNotEndpoint.lean` and `OneNotComputation.lean` await the root combined module build, then will be compiled independently. These supplement proofs are not yet kernel checked.
2026-11-25 20:08 UTC resource/certificate progress:

- The specialized `live_certificate_false` / one-NOT endpoint is kernel checked. The monolithic one-NOT computation exceeds available memory, so the same search is split through generic continuation cuts whose reconstruction identities are separately proved.
- All 54 unary-first leaf checks passed (`CompactUnaryChecks.lean`, about 29 seconds kernel time), and the arbitrary-continuation unary coverage check passed. The largest unary leaf has 519 Python search states and takes 1.18 seconds kernel time.
- Binary-first search is split into 42 parents and 3,199 distinct second-level leaves. All exported Python results are false; the largest leaf has 4,061 states and passed Lean in 8.59 seconds using direct constants. Generic patched-continuation glue is being checked by repo_review; final validity will depend on Lean coverage checks, not Python enumeration alone.
- Direct 6,000-state grouped checks with large flat array tables exceeded the 6,000 MB Lean cap. All-field W normalization (`frcAll`, including the rank field), explicit noncomputable data, and a six-stage counter decoder improve runtime, but the 6,000-state flat-table check still exceeded the cap. A corrected compact 4,061-state check passed with peak 4,864,540 KiB and 13.8 seconds kernel time.
- Pinned Lean source confirms Array is list-backed in the kernel. finite_search produced `CertificateDataChunked.leanfrag`, splitting large tables into 64-entry chunks while preserving every entry and index. This variant is awaiting kernel benchmarks and coverage checks. The current common fragment is 230,522 bytes.
- Lower-bound 13 has also been split safely: all 21 zero-NOT children plus coverage passed in 74.9 seconds, and the remaining 12 NOT-count checks passed in 15.2 seconds (proof_route). The root can replace the memory-heavy conjunction with these separately checked proofs.
- Duplicate truth samples cannot simply be removed: they make positive and negative row groups simultaneously contiguous for the engine's carry-based flag computation. No unsound deduplication was attempted.

All complete compiler logs remain under `/tmp/oec/pequalnp-pilot-178/`; the root is preserving checked sources and logs on the authorized branch. This agent has made no desk, git, or credential calls.

2026-11-25 20:36 UTC: certificate source frozen for the first full named build.

The chunked table backend passed a 6,000-state group, but large batches were slower than separate checks. On the same 18 leaves: one group took 35.8 seconds kernel time, while 18 separate checks took 28.0 seconds. Strict recursive normalization was proved equivalent and tested, but gave no further speed improvement, so it is omitted from the final implementation. A decode-only control took 0.789 seconds, isolating the remaining cost to search checking rather than table reconstruction.

Two asynchronous theorem bodies, each checking a 3,000-state group, passed with peak 4,399,664 KiB. Their individual kernel times were 9.94 and 9.07 seconds, and the main process reported 9.97 seconds blocked waiting. The final plan uses small groups in exactly two lanes, with all other computational checks ordered before those lanes.

Final binary partition: 579 groups. Seven unavoidable single leaves exceeding 3,000 search calls are checked synchronously first. The other 572 groups use a conservative fresh-call budget of 1,000, except individual leaves between 1,000 and 3,000, and are balanced into two lanes of 286 groups each (264,951 and 264,944 fresh calls). The exact index-mask coverage of all 3,199 leaves and the three-way proof combination passed in `FinalBinaryGlue.lean`; full leaf execution is intentionally deferred to the named-file build.

Frozen scratch inputs:
- `finite_search/CertificateDataChunked.leanfrag`: 64-entry table chunks; explicit noncomputable data; six-stage counter decoder.
- `certificate_search/StrictNormalize.leanfrag`: checked strict Nat forcing and all-field W normalization.
- `certificate_search/IndexedUnaryFinal.leanfrag`: 54 unary checks using shared indexed data (the same values previously checked directly).
- `certificate_search/BinaryFinalPrefix.leanfrag`: checker wrappers, partition data, checked mask equality, and seven synchronous outliers.
- `certificate_search/BinaryFinalLanes.leanfrag`: exactly two asynchronous lemma bodies, each with sequential small kernel checks.
- `certificate_search/BinaryFinalAssemble.leanfrag`: logical combination and original look/look1 leaf interfaces.

Use the reviewer's 42 individual closed coverage definitions in `lrat_route/BucketCoverage.leanfrag`. Combined all-42 and six-batch experiments were interrupted and are not final inputs. Generic restoration, exact two-mask endpoint, lower13 split, and final binary combination have all passed separate smoke tests. No long Lean job remains owned by this agent; the root has the sole compile slot for the full proof.
