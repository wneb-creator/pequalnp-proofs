# Final preservation report

Kit message acknowledged: msg-5c117df1f45d6a72cccf81e5.

No full proof or refutation was found. No PR was opened. The initial L-meta-1035 status check did not establish a recorded refutation; that gap was never assigned here, so no six-input counterexample was re-derived. This branch is an artifact-preservation branch and is NOT a valid single-file proof PR.

## Desk stop condition

Two returned leases became invalid with HTTP 410 despite recent successful renewals. The first was for L-meta-2592 (error14:39:57 UTC; prior renewal expiry 14:55:23). The second was for L-meta-2583 (error15:06:10 UTC; prior renewal expiry 15:22:18). Exact body in both cases:

    {"error":"no such live lease: it expired or was released. Ask /desk/next again."}

Complete unabridged headers and bodies are saved in validation/desk-error.txt, validation/beat-15-diagnostic.txt, validation/desk-error-new.txt, validation/beat-new-05-diagnostic.txt and desk-log.txt. Each failed call was repeated once with curl-si as instructed. Checked work was pushed before each recovery request.

Second recovery returned L-meta-2590 with issued_at 15:07:28UTC, before our request, and holding = 5. Its exact note:

    you hold 5 gaps, the most one handle may hold at once; release one to get another

One required ownership retry returned the SAME gap and SAME lease with the SAME note. We cannot establish this is a distinct lease belonging to this pilot. Per the brief, stopped without working on or releasing L-meta-2590. One beat was sent before this ownership concern was recognized; no subsequent renewal or release was sent. No release was sent for either invalidated lease, and no other pilot lease was deliberately released. Null desk responses: 0. Full responses are preserved in validation/desk-recover-2.json and validation/desk-ownership-retry.json.

## Checked artifacts and limits

- lean/PEqualNP/Outside/L_meta_2592.lean: 5337 lines. lake build passed (validation/partial-build-03.txt). Stronger 17-binary-gate floor and conditional 18 bounds were compiled in development components under lemmas/Floor17*, Floor18 and FloorSecond; these require concatenation/development module setup and are not a full posted proof.
- lean/PEqualNP/Outside/L_meta_2583.lean: 2522 lines, exactly the independently reviewed PlaneBundle.lean. The bundle compiled successfully as a standalone source (validation/plane-bundle1.out/.err). The latest named-module lake build was the preceding 326-line version and passed (validation/plane-partial-build-02.txt); the 2522-line copy was not rebuilt under the named module after the desk stop. It proves exact plane READ1 lower bounds and the concrete Fano READ1 minimum 27, plus incidence/geometry helpers. It does NOT prove arbitrary AO2 replacement.
- Complete independent reviews, source provenance, finite Fano/symmetry checks, normalization obstructions, and solver generators/decoders are in results/orch/.
- Existing checked Petersen circuit L584 was independently verified:13 OR + 7 AND, 15 edges, no 4-cycle, exact 1024-row truth table. This refutes only the proposed generic C4-free OR-count bound, not either assigned statement.
- All 21 saved Fano 26-gate candidates fail exactly 47 of 16,384 inputs (one omitted incidence edge); none is a counterexample. SAT and heuristic runs were interrupted after lease invalidation; UNKNOWN/interrupted is not a proof. Fano 19-OR/free-AND search was prepared and reviewed but NOT RUN.
- StructuralAdjacentOr.lean is explicitly UNVALIDATED (canceled exit 143). It is preserved as scratch and not included in checked claims.

## Checker and cleanup

Official tools/check-lean.mjs ended CHECKER FAULT, exit 3: full Mathlib statement environment could not load Batteries.olean. Full output is validation/partial-checker-01.txt (and checker-limitations.md describes the storage blocker). No accepted checker verdict exists. Latest format guard REFUSED the plane file for copied top-level helper declarations outside its permitted namespace layout. The final posted theorem is also absent. Full output: validation/plane-format-final.txt. These layout problems remain in the preserved development bundle; it is not submission-ready. The guard refusal was not bypassed and no PR submitted.

Cleanup was skipped because there is no full result and the official checker cannot run with the available full-library cache. Cleanup line counts unchanged: 2592: 5337 -> 5337; 2583: 2522 -> 2522. No Mathlib source build, lake update, sorry, new axiom, or native_decide was introduced.

## Measurement

Sub-agents: counterexample_search, lemma_routes, reduction_strategy, restriction_review, status_review, structural_proof
TIMING total=88.5 subagents=6

End reason: explicit desk ownership stop condition, not a claimed proof or missing-lemma release. All searches and renewal loops stopped. Latest proof/artifact checkpoint before this report: 0133886e7991ab1771364f3643f7862b4a9c92e4 on pnp/pilot-100, pushed to origin.
