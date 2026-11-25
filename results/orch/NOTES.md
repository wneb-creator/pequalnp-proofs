# L-meta-2592 orchestration

Attempted task: Petersen edge function, no fan-in-two circuit of size at most 19 with a NOT gate. No own lease was established: the returned lease predates this job, and the one permitted another=1 retry returned the same lease. Work stopped under the owner's existing-lease rule; it was not released.

Strategies: repository implication search; structural lower-bound proof; counterexample/SAT search; reduction decomposition.

Append timestamped findings; agents use separate files in results/orch/lemmas. Never modify the final proof file concurrently.

2026-11-25T14:28:55.367393+00:00 counterexample: reviewed Circuit/FanInTwo semantics. No immediate loophole. Preparing 1024-row truth-table stochastic synthesis, seeded with size-20 vertex-cover/star constructions. SAT route awaiting possible cadical in Lean distribution.

2026-11-25T14:29:07.024071+00:00 — status_audit

### Repository implication audit
- L-meta-1035 is already refuted by paired L-meta-1036, merged PR 2095, commit f463ca8b (2026-11-23T19:59:07Z). No exact 1035 match among 914 currently open PRs.
- R_meta_2592_271 splits this task into binaryFloor and fewNot. The binaryFloor child is ALREADY PROVED in L_meta_4725.lean: every full Petersen FanInTwo circuit satisfies 15 + notCount C ≤ C.size (3224 lines, only Defs and Mathlib imports). Therefore the task reduces to 1–4 NOT gates.
- fewNot is L-meta-4727; no accepted L_meta_4727.lean exists. Its three reductions R_meta_4727_{1,17,53} are present. The signed normal form 53 counts negated wire marks; reduction 17 compiles semantic function tables with at most k free complements and at most 19-k binary operations.
- Existing cofactor lower bounds: L_meta_8033 proves Petersen-minus-vertex size ≥15 and 13 + notCount ≤size. L_meta_8039 excludes its size=15, notCount=2 case. L_meta_2541 excludes size≤14 when one input has ≤1 reader (either polarity); L_meta_2850 is its flipped-input case.
- For normalized full Petersen with first OR gate x0 OR x2: L_meta_5236 excludes 3–4 NOT and remaining budget≤18; L_meta_5238 excludes ≥5 NOT. These do not discharge arbitrary first gates or 1–2 NOT.
- Exhaustive bounded repository statement scan among L_meta files mentioning 10 inputs found no accepted full Petersen 19-gate exclusion or 20-gate lower bound. L_meta_8021 is vacuous (assumes no NOT and notCount≥1), not a route.
- Desk reductions_live=3 already reaches the documented maximum. A fourth reduction should not be assumed admissible solely from reductions_open=true.
- Full search evidence saved under /tmp/oec/pequalnp-pilot-123/audit-*.json and audit-*.txt.

2026-11-25T14:29:13.897365+00:00 decomposition: three reductions already live (318 last-NOT separator, 408 legal normalization, 271 binary-floor/few-NOT). User cap prohibits a fourth. Pursuing NOT-aware support bound: n−1+notCount≤size for all-input-dependent functions; Petersen specializes to 9+notCount≤size.

2026-11-25T14:30:01.915841+00:00 structural: Petersen has independence number 4 (five maximum independent sets), hence vertex-cover number6. Exhaustive Python confirms all180 ordered (fixed variable, other variable, fixed value) cofactors depend on the other variable. Full-basis graph theorem EdgeFnGraphPlan only handles T7 (girth≥7, high-degree vertices distance≥7), so not Petersen. Lean finite-fact scratch at structural_petersen.lean pending toolchain.

2026-11-25T14:30:09.877332+00:00 lean_setup: Kit warm image absent (no elan, Lean, .lake, or prepared marker; initial disk only 819 MB). Installed official Lean v4.36.0 portable release in /tmp/oec/pequalnp-pilot-123/lean-4.36.0-linux; cadical included. Prefix commands PATH=/tmp/oec/pequalnp-pilot-123/lean-4.36.0-linux/bin:$PATH XDG_CACHE_HOME=/tmp/oec/pequalnp-pilot-123/cache. First lake exe cache get underway; no lake update or Mathlib library source build.

2026-11-25T14:30:42.261210+00:00 — status_audit

### Refined full-Petersen bottleneck
- Completed final-declaration census of every accepted L_meta file mentioning ten inputs (both theorem and lemma; zero missing declarations). No accepted arbitrary 1/2/3/4-NOT full Petersen exclusions were found.
- R_meta_4727_1 is an unhelpful zero-NOT / has-NOT split: its accepted first child L_meta_8021 is vacuous. Second child is essentially fewNot again.
- R_meta_5234_1 (1214 lines) is the first-OR(x0,x2), 1–2-NOT branch. Its first hypothesis is 9-input strict deleted-Petersen ≤15,≤2NOT exclusion, now supplied by L_meta_8367 (decomposition agent). Remaining hypotheses concern strict 11-input residual circuits on x plus x0 OR x2: not0,size17; not1,size17..18; not2,size17..18, with final output and small input-reader counts. None of these full-10 residual hypotheses has an accepted proof found in current tree.
- R_meta_5150_1 now closes the full Petersen fixed-zero cofactor ≤15 claim from accepted 9-input ≥16 facts (L8033 + L8035/8037/8039). However no implication closing the strict residual full10 cases was found.
- Actual known general full10 binary floor remains 15 binary gates; with total≤19 there are at most4 NOTs. A proof still needs nontrivial sharing/reader restrictions or a finite lower-bound certificate in the remaining configurations.

2026-11-25T14:30:46.096682+00:00 lean_setup: SUCCESS lake exe cache get exit 0, all 9117 artifacts downloaded and decompressed; 18 GB free. Checker shim requires PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-123/lean-4.36.0-linux/bin/lake and PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-123/pnp-build (plus prior PATH and XDG_CACHE_HOME). Full logs /tmp/oec/pequalnp-pilot-123/setup-cache.stdout and setup-cache.stderr. No tracked file modifications.

## Research status — 2026-11-25T14:31:49.272468+00:00

Read https://pequalnp.com/papers/note-1 on 2026-11-25; saved full HTML at /tmp/oec/pequalnp-pilot-123/research-note-1.html. Its checked full-basis graph lower bounds cover forests and separated hubs / long cycles, not Petersen. General monotone quadratic negation elimination was not found in allowed-host primary-source searches. Markov inversion complexity concerns the number of NOT gates, not total size, so does not justify eliminating NOT gates without cost.

A candidate targeted route (UNVERIFIED; no proof): in the first-NOT-on-input case, restricting that input to false deletes the NOT and its direct readers. With deleted-Petersen cofactor lower bound 16, four deleted gates rule out total size 19. The equality case appears to force one neutral positive reader p=x OR u and one neutral negative reader q=(NOT x) AND v; then use the exact monotone cofactor equality structure to exclude reinsertion in only three gates. Generic fanout 3/4 alone yields only a 19-gate floor. Sent this to structural agent and root.

Paused immediately at root instruction while lease ownership is clarified.
