L-meta-650 orchestration

Lease obtained 2026-11-25T02:14:27.889Z. Root alone contacts desk and submits.
Target: AND/OR circuit size <= 63 for 26-input order-3 projective plane incidence graph. Baseline expected 64.
Allowed project import: PEqualNP.Defs. reductions_open=true, reductions_live=3. Existing reductions: R_meta_650_1, R_meta_650_517, R_meta_650_713.
Each agent appends findings using its name and timestamp; keep individual scratch in results/orch/lemmas/<agent>/. Root owns final L_meta_650.lean.
Lean command environment: ELAN_HOME=/tmp/oec/pequalnp-pilot-57/elan PATH=/tmp/oec/pequalnp-pilot-57/elan/bin:$PATH. Mathlib cache ready. Root building PEqualNP.Defs.


## status_review 2026-11-25T02:16:27+00:00

Independent red-team review of the posted L-meta-650 target and current definitions:
- The target is existential over Circuit; the same fixed C must work for all 26-input Bool vectors. Size is exactly C.gates.length, including unused and constant gates. Inputs are not counted.
- Monotone2 requires every listed gate to be AND or OR with inputs.length <= 2. Empty AND=True, empty OR=False, unary copying and repeated references are permitted. No separate well-formedness hypothesis appears.
- Invalid/future references legally read false in the current intermediate list. Evaluation is foldl, not a recursive/fixed-point interpretation. A future reference never retrieves the later gate. Output outside the completed wire list is false. These choices are explicit in CircuitLowerBounds.lean, so legitimate witnesses may use them, but they do not provide hidden higher fan-in or feedback.
- Exact posted graph has 52 ordered pairs from points 0..12 to lines 13..25. A correctness proof must establish the iff on all Boolean assignments; positive edge tests alone are insufficient.
- Current desk row says reductions_live=3; all three upstream files R_meta_650_1, R_meta_650_517, R_meta_650_713 exist. The user/site limit is three live reductions per step. A fourth reduction is not a viable submission while this count holds, despite reductions_open=true.
- Only PEqualNP.Defs is an allowed project import. Existing R_meta_650 files can be studied but may not be imported into this proof. Mathlib modules are permitted.
- Checker elaborates the recorded statement against pinned Mathlib plus the definitions root; then kernel-checks the candidate constant at that target type in an environment extended only by rechecked declarations. Candidate-local definitions/instances cannot redefine the target meaning. Reduction mode additionally demands structural target equality and restrictive child predicates.
- Main theorem must be fully qualified and last at top level. All helpers must sit inside the file's own namespace, with explicitly named closing end lines at column zero. No prohibited raw text (_root_, quotes, etc.).
- Before each early push, review source and diff. Final submission must add only named L_meta_650.lean relative to upstream; results artifacts must be preserved in earlier pushed history and removed from final diff. No final proof or candidate has yet been reviewed.

[reduction_analysis 2026-11-25T02:17:02.334591+00:00] Existing R650_1 and _713 are duplicate geometry+finite-search cuts; _517 uses 25-input residual circuit with two jointly computed outputs at cost <=61 then 2-gate attachment. Residual baseline59 plus separate tap3=62, so hard saving remains. Computed geometry check:
UTC 2026-11-25T02:17:02.333949+00:00
Max compatible opposite side by point-set size: {0: 13, 1: 9, 2: 6, 3: 4, 4: 3, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1, 10: 0, 11: 0, 12: 0, 13: 0}
Maximal incidence-free rectangles: 704
Rectangle sizes: {(0, 13): 1, (1, 9): 13, (2, 6): 78, (3, 4): 234, (3, 3): 52, (4, 3): 234, (6, 2): 78, (9, 1): 13, (13, 0): 1}

2026-11-25T02:17:15.895271+00:00 lean_baseline: Compiled explicit baseline of 64 gates; Monotone2 and exact size proved in lemmas/lean_baseline/Baseline.lean. Semantics development continues separately in BaselineCorrect.lean.

[status_review 2026-11-25T02:17:38+00:00] APPROVED early partial snapshot: Baseline.lean has 64 binary AND/OR gates and valid preceding-wire references; output 89 matches exactly the posted 52 edge minterms in an independent symbolic computation. Lean lemmas claim only size64 and Monotone2, with no prohibited proof constructs or axioms. NOTES/TIMELINE reviewed. This is preservation of a partial result, not a size63 witness or a PR-ready file. Validation file must record that distinction.
2026-11-25T02:18:00.681403+00:00 circuit_search: Enumerated 704 maximal independent sets and52 edge positives;756-bit basis exactly certifies final monotone output. C++ search.cpp runs63gate stochastic synthesis from random64gate star circuits with oneORgate removed; neutral mutations, three annealing phases, restart every1m candidates. Started02:17UTC for600s; best at52m attempts remains one missededge/no false inputs. No Lean result yet.

2026-11-25T02:18:26.255435+00:00 lower_bound: semantics audit found no invalid-wire/constant shortcut. Existing L_meta_613 m+cover bound needs centered edge-safe ANDs and no nested AND dependence; cannot assume general bound. GraphFacts.lean compiled: exact52edges, row/column4, pairwise row intersection1, explicit perfect matching. Full refutation remains unproved.

[status_review 2026-11-25T02:19:01+00:00] APPROVED partial snapshot GraphFacts.lean and BaselineCorrect.lean. Independent exact-list and combinatorial checks confirm 52 distinct posted edges, degree4 both sides, distinct row intersection1, explicit perfect matching13. BaselineCorrect duplicates the approved64-gate data and proves its eval equals the exact13-star formula for arbitrary x. No forbidden constructs/new axioms. Both build logs inspected (empty, successful exit0 reported). These do not prove the size63 target.
2026-11-25T02:19:05.533406+00:00 lean_baseline FINISHED: BaselineCorrect2.lean compiled exit0, proves explicit64-gate circuit, exact size64, Monotone2, symbolic eval formula, and exact posted52-edge correctness for all Fin26 Boolean inputs. Correctness uses symbolic simp, not assignment enumeration. Source frozen for root review/push; log /tmp/oec/pequalnp-pilot-57/baseline-correct2-build.log is empty success.
2026-11-25T02:19:16.786845+00:00 algebra_strategy: Produced 26 correct 66-gate final-AND absorption seeds in results/orch/lemmas/algebra_strategy/nested_and_seeds.json, validated on all52 minimal positives +704 maximal negatives (exact monotone basis). H is36-edge residual after deleting center +4neighbors, built with44gates; final expression (H OR center OR four residual neighbor stars) AND (H OR four neighbors). Larger than64 baseline but distinct mixed-intermediate topology for search. Standard pure biclique factoring cannot save because noC4.

2026-11-25T02:19:24.822073+00:00 lower_bound: GraphFactsCover.lean compiled with every exact-incidence vertex cover cardinal >=13, by explicit matching injection. Original GraphFacts frozen for root review/push.

[status_review 2026-11-25T02:19:59+00:00] APPROVED newest partials BaselineCorrect2.lean (SHA256 bff9521fa0eff94d700035a21116970c98fe5beef91e74886e3843a513af2d3d) and GraphFactsCover.lean (SHA256 9b566ed6df4928e4930ec7dbf0ee5c2fd8d95af658fc6c6e48ae37a7ec3ebaab). Baseline exact52edge iff holds for arbitrary x by ordinary simp; cover lower13 uses injection choosing matching endpoints. Deltas and full-file exact graph/forbidden text checks pass; success logs inspected. These establish size64 upper witness and cover13 partial facts, not targetsize63.

[reduction_analysis 2026-11-25T02:20:34.044925+00:00] COMPILED Geometry.lean: incidentLines_card=4, distinct pair intersection=1, and independent_rectangle_small via four-set inclusion-exclusion. lake env lean returned0; no diagnostics, log /tmp/oec/pequalnp-pilot-57/geometry-build.log. Initial exhaustive715-subsets proof was stopped at12GBRSS; final structural proof uses only13 and169 finite cases and succeeds. Root notified for independent review and immediate push.

[status_review 2026-11-25T02:21:04+00:00] APPROVED Geometry.lean partial, SHA256 db947785ca2abcbb7341921c9ceb0ea55d06a91502138ae042fcf34bf650a0af. Modular p+l in {0,1,3,9} matches exact posted52 edges. Independently checked degree4/intersection1 and exhaustive subset rectangle bound. Lean proof uses four-row union cardinality>=10 then disjointness in Fin13 to bound opposite side<=3; only small finite geometry uses decide+kernel. No prohibited constructs/new axioms. Empty successful build log inspected.

[reduction_analysis 2026-11-25T02:21:08.575158+00:00] Residual two-output finite test pack written residual-tests.json. {"residual_pos": 48, "residual_neg": 553, "tap_pos": 4, "tap_neg": 197, "union_tests": 756, "tap_neg_sizes": {"(0, 9)": 1, "(1, 6)": 12, "(2, 4)": 54, "(2, 3)": 12, "(3, 3)": 72, "(5, 2)": 36, "(8, 1)": 9, "(12, 0)": 1}}
