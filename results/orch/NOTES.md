# L-meta-2592 orchestration notes

2026-11-25 14:13 UTC: Leased L-meta-2592. Goal: lower bound 20 for Petersen edge circuits containing NOT. Three reductions already live, so fourth reduction not available. Strategies: structural lower bound, computational counterexample search, semantic normalization, root integration/checker.

2026-11-25T14:15:25.886658+00:00 normalization: Draft generic cut_last_not decomposition in results/orch/lemmas/normalization/LastNot.lean. Invalid wires/empty NOT inputs do not refute statement: choose prefix output n+pre.length for empty NOT input. Awaiting Lean runtime verification.

2026-11-25T14:16:19.764516+00:00
## Structural strategy
- Existing checked source `L_meta_4725.lean` proves the full Petersen binary-gate floor: `15 + notCount C ≤ C.size`. Prepared a renamed self-contained copy plus `high_not_impossible` in `lemmas/structural/L_meta_2592_partial.lean`; compilation awaits toolchain/cache setup.
- Consequence: the target is already ruled out for five or more NOT gates. Remaining cases use one through four NOT gates.
- General edge-function bound from https://pequalnp.com/papers/note-1 (read 2026-11-25) requires forests, cycles, or sufficiently long cycles/hub paths. Petersen's girth five and adjacent degree-three vertices fall outside the hypotheses.
- Do not mistake `L_meta_9781` for a full Petersen20 lower bound: its internal `mono_floor` is a nine-input cofactor bound16, and its final statement handles the Petersen graph with two adjacent edges removed.

2026-11-25T14:16:53.177571+00:00 normalization: Draft trim_output at results/orch/lemmas/normalization/TrimOutput.lean removes every gate beyond the output without size increase and preserves all evaluations; pending Lean cache. Combined with constant propagation it handles output-normalization part of R_meta_2592_408.

### Counterexample search 2026-11-25T14:18:23.139643+00:00
- Verified all 1024 truth-table rows. Petersen has 76 independent sets: 1 empty, 10 singleton, 30 pairs, 30 triples, 5 quadruples. Exactly 15 maximal independent sets.
- Running C++ stochastic 19-gate AND/OR/NOT search requiring NOT; best weighted error 30, no witness so far. Complete log: /tmp/oec/pequalnp-pilot-116/stochastic-116.log.
- Running Cadical CEGIS on 42 critical patterns (15 edges, 15 maximal independent sets, 10 singletons, empty/full). 3173 variables and 74038 clauses. Every candidate checked on all 1024 rows. General1–4NOT and exact1NOT essential-operand-pruned instances both active. Source: results/orch/lemmas/search/synthesize.py.

2026-11-25T14:19:56.785682+00:00 [few_not_analysis] Prepared ComparableNot.lean (104 lines), uncompiled pending Lean installation: endpoint constant replacement under output/operand implication, essential NOT implies incomparable assignments, edge and maximal-independent-profile necessary conditions. Petersen has 76 independent sets and 15 maximal independent sets, masks [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773], independently enumerated in scratch. Search agent incorporated one-NOT profile pruning. No general one-NOT cost-preserving elimination theorem found; existing small cases rely on explicit lower bounds.

- Structural follow-up: `lemmas/structural/MonotoneWires.lean` drafts monotonicity for arbitrary AND/OR gate lists, the actual circuit splice `Q.eval (P.wires input ++ [z])`, and the fact that a list with exactly one NOT has no NOT in the prefix/suffix around it. These bridge the normalization and endpoint strategies. Awaiting cache to compile.

### Search checkpoint 2026-11-25T14:23:00.477307+00:00
- Both stochastic processes stopped for cache/build CPU. Original best had18 mismatches, active-NOT best had21; neither is a counterexample. Active near-miss saved to results/orch/lemmas/search/near_miss.json with mismatch list and explicit warning.
- SAT runs continue. Both are witness searches with normalized topology assumptions, so an UNSAT answer alone would not prove the posted statement. In particular, dead NOT plus18-gate monotone circuit is not covered by the no-dead-gate SAT model.
- SAT encoding sanity-checked with a planted10-gate circuit on all1024 inputs; Cadical returns SAT as expected. All stdout/stderr preserved in /tmp/oec/pequalnp-pilot-116/encoding-validation.log.

2026-11-25T14:23:20.486927+00:00 [few_not_analysis] Read https://pequalnp.com/papers/note-1 through web search. General checked no-NOT-cost result there is limited to long cycles and well-separated degree>=3 hubs; it does not apply to Petersen (girth5, adjacent degree3 vertices). ComparableNot now147lines, narrow Mathlib imports, compile blocked only by missing Bool.Basic.olean while root cache downloads. Essential-NOT endpoint pruning remains conditional on essentiality; unrestricted search must also consider dead-NOT padding of a hypothetical <=18 monotone circuit.

2026-11-25T14:23:32.570896+00:00 normalization: LastNot.lean now tracks exact NOT count and includes cut_only_not with both prefix and suffix Monotone2. Independent source reviewer prior_status found no semantic or plain-format issues; still awaiting root cache/build readiness.

2026-11-25T14:24:37.157533+00:00 restriction_route: InputOccurrences.lean compiles with pinned Lean4.36 (exit0, no imports). It proves list count domination gives length domination, then a live trace with s<=19 and effective fanin<2*s must have an input read at mostonce; if all ten inputs are present, exactlyonce. Application requires normalizing ignored second NOT operands and removing dead gates. No full Petersen lower bound yet. Unconditional Petersen-minus-vertex bound found is15 (L_meta_8033), binary13; specific firstgates yield16.

2026-11-25T14:26:04.384001+00:00 restriction_route: GateInputOccurrences.lean (116 lines) compiles pinnedLean4.36 exit0. Strengthens first partial by deriving strict total fanin from width<=2 plus a width<=1 gate. Final live_gate_trace_unique_input uses ordinary nested list of effective wire reads, proves unique-read essential input for live<=19 trace. No Mathlib needed, no admissions. Applying to arbitrary circuit still needs normalization (discard ignored NOT operands and unused gates) plus semantics to establish all inputs essential.

2026-11-25T14:26:12.890280+00:00 [few_not_analysis] ComparableNot.lean compiles under Lean4.36, exit0, empty output. SHA256 6a794c85ccb8a03057479f4265c5e47e354ac496b9adb30a08b5a55149f9a288. Independent reviewer checking final edits. New CircuitEndpoints.lean40-line companion pending Defs build.

2026-11-25T14:28:01.874244+00:00 restriction_route: graph_stats.py exhaustively checked all10 zero-cofactors:12edges, independence4, minimum vertexcover5, star upperbound16. Setting one vertextrue leaves its3 neighbors as freeOR terms and residual6vertices/6edges degree2. Gap to proof: liveunique-input counting alone gives only parentboundary constraints; no valid argument yet that three-neighbor operand gates are private or that restriction deletes4gates. NOT gates/shared circuitry block a naive monotone charging argument. Structural agent exploring exact-sixbranch polarity rigidity separately.
