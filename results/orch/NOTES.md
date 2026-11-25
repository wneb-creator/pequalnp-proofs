# Pilot 59 orchestration

Gap: L-meta-1031. Root alone owns and renews the lease.
Statement and desk answer: /tmp/oec/pequalnp-pilot-59/desk-001.json

Append findings with your strategy name and UTC timestamp. Distinct scratch files only. Never edit the target proof without root approval.

## Minimal-existence strategy 2026-11-25T02:26:42.998164+00:00

L_meta_2666 proves existence of a minimum monotone circuit for every finite graph (150 lines), so existence is not an open obstacle. L_meta_2668 lost_edge proves every gate of such a minimum is essential on some positive edge input; the AND hypothesis in its final theorem is unused. Prior pilot56 Prune.result cleans globally sound AND circuits with no size increase, without using minimality or girth assumptions. Its minimum_last_gate_sound already covers the last AND (all later gates OR), not merely the final gate. Working on dependency-cone strengthening.

## ownership_exchange — 2026-11-25T02:26:53.650371+00:00

Read existing reductions 1–3. Reduction 2 already proves stars from semantic soundness of every AND plus pruning of non-owning ANDs. Pilot56 `Prune.result` completes that pruning; `finish_from_pair_normalization` leaves exactly existence of a least circuit in which each AND accepts only genuine graph edges on inputs of weight at most two (including repeated endpoints). The graph-only rectangle-to-star argument uses C4-freeness; triangle-freeness is only needed by any future normalization argument.

A caution for exchange attempts: replacing an unsound AND by an operand generally increases accepted negative pairs. Example on path b-c-a-d: `(a∨b)∧(c∨d)∧(a∨c)` computes edges ac,ad,bc but has an unsound intermediate rectangle AND. It uses 5 gates, while star construction `a∧(c∨d) ∨ b∧c` uses 4. Thus a useful proof must charge the later filter against a rewrite, not claim all ANDs of arbitrary circuits are sound.

Research context, read 2026-11-25: Jukna, *Disproving the Single Level Conjecture* (SIAM J. Comput. 36(1), 2006), abstract at https://web.vu.lt/mif/s.jukna/ftp/single1.pdf and https://eccc.weizmann.ac.il/report/2005/021/ confirms that normalization to one AND layer is false for unrestricted quadratic Boolean functions. This does not refute the current girth≥5 statement; no applicable theorem for that restriction was found. PDF full-body retrieval timed out; any stronger applicability claim is UNVERIFIED.

Root 2026-11-25 02:27 UTC: recovered public pilot56 helper file from PR11479, commit d585ca8aad082f3ec25bb50596d0824f8cfdf437. The PR was refused before build because it contains no final theorem. Copied helpers to target only as a partial baseline for validation; no claim of full gap proof. Gap normalization remains unresolved.

## Constructive strategy 2026-11-25T02:27:51.775543+00:00
Canonical direct-edge ownership and star-graph optimum already exist in pilot56 partial. New direction: arbitrary matching graphs, whose endpoints are pairwise distinct. Optimized direct-edge circuit has 2m−1 gates; all 2m endpoints are essential, so dependency counting gives lower bound 2m−1 for every fan-in-two circuit, even with NOT. This establishes the entire ownership/minimality statement on matching graphs, a multi-AND subclass beyond stars. Draft standalone scratch at results/orch/lemmas/constructive_matching.lean; awaiting Defs build to check.

## Counterexample search 2026-11-25T02:27:56.087103+00:00

No defect found for n=0 or edgeless graphs: the empty gate list with output n computes false with minimum size zero, and ownership is vacuous. Forward gate reads evaluate false; the posted ancestry relation excludes these reads via increasing wire indices and matches the definitions.

Exhaustive semantic-set BFS on four inputs: 9,406 states through four gates, all 37 nonempty labelled triangle/C4-free graph edge functions found with minimum witnesses. Every chosen minimum witness satisfies nonempty star ownership. Five-input BFS through four gates: 67,336 states, 170 of 302 nonempty labelled eligible graphs found, every witness has nonempty star ownership. Remaining 132 need more gates. These are computational checks, not Lean certificates; omitted constants/unary/duplicate operations are redundant in a minimum circuit for a nonconstant function.

Scripts: results/orch/lemmas/counterexample_small.py and counterexample_milp.py. Complete logs in /tmp/oec/pequalnp-pilot-59/counterexample-*.stdout and .stderr. A 300-second HiGHS search for a six-gate five-cycle circuit is running after root renewal.

## minimal_existence — 2026-11-25T02:29:45.214305+00:00

NEW CHECKED COMPONENT: results/orch/lemmas/minimal_cone.lean (510 lines) compiled with lake env lean, exit 0. Complete output: /tmp/oec/pequalnp-pilot-59/minimal-cone.stdout and .stderr. Namespace PEqualNP.Outside.L_meta_1031_aux.Maximal. New wireStep/downstream_difference/minimum_top_gate_sound strengthen pilot56 last-AND soundness to every gate having only OR gates strictly downstream in its dependency graph; unrelated later ANDs are allowed. The proof traces an essential edge lost by deleting the source gate and records a dependency path at each changed wire. Any changed downstream AND contradicts the hypothesis, and an OR path propagates source truth on every input. Uses no girth hypothesis. Every-edge ownership is separately already proved in L_meta_1599 for arbitrary AND/OR circuits computing a graph edge function (no fan-in or minimality hypotheses).

### Counterexample update 2026-11-25T02:30:24.851437+00:00

Exhaustive five-input BFS through five gates reached 963,440 semantic states and minimum witnesses for all 290 nonempty eligible forests; all chosen witnesses have nonempty star ownership. The only remaining 12 labelled eligible graphs are C5. A final scan of every possible sixth gate over all 896,104 depth-five states found no C5 realization. A direct seven-gate C5 witness was independently reevaluated on all 32 inputs and has the posted nonempty star property: [('or', 1, 4), ('and', 0, 5), ('or', 1, 3), ('and', 2, 7), ('and', 3, 4), ('or', 6, 8), ('or', 9, 10)]. Thus no counterexample exists through five vertices under the standard redundant-gate elimination argument; this evidence is not yet formalized in Lean.

The separate HiGHS circuit encoding also reports six-gate C5 infeasible (87.5196 seconds, status 2), agreeing with BFS. Complete diagnostics remain in scratch. A fixed bad-prefix seven-gate search tests the stronger all-minimum-circuits variant.

## ownership_exchange — 2026-11-25T02:31:00.747575+00:00

CHECKED: `results/orch/lemmas/exchange_readonce.lean` passed Lean (exit 0). New extension starts after pilot56 base at line3029: positive De Morgan formula compilation into exactly leaves−1 gates; arbitrary graph incident-vertex lower bound; `compact_formula_minimum` proves any positive graph formula using no more leaves than incident vertices produces a least monotone circuit. This includes the optimality argument for star forests represented by read-once formulas. It does not yet assert star ownership. Full logs: `/tmp/oec/pequalnp-pilot-59/exchange-readonce.stdout` and `.stderr`.

## Constructive strategy 2026-11-25T02:31:22.292043+00:00
Matching exact optimum compiled (original 685 lines; first cleanup 514 lines). Full logs: /tmp/oec/pequalnp-pilot-59/constructive_matching_compact.stdout and .stderr. Now extending from explicit edge list to intrinsic max-degree-at-most-one hypothesis, via oriented edge enumeration and endpoint-disjointness.

Research read 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf. It proves large general gaps between single-level and unrestricted quadratic monotone circuits, using saturated graph constructions; these have triangles and do not directly settle the leased triangle/C4-free problem. Exact single-level normalization must not be assumed merely because the target function is quadratic.

## Constructive strategy 2026-11-25T02:32:06.945500+00:00
Intrinsic maximum-degree-one result now compiles too. `Matching.degree_one_optimal` proves the entire posted ownership/minimality conclusion from `∀ u v w, G.Adj u v → G.Adj u w → v = w`, via a fully proved oriented-edge enumeration. File: results/orch/lemmas/constructive_matching_compact.lean; Lean exit 0. This is only a matching-graph subclass, not the unrestricted L-meta-1031 theorem.

## pair_normalization — 2026-11-25T02:33:55.585021+00:00

Lean-checked new component `results/orch/lemmas/pair_three_cnf.lean`: any triangle-free graph whose edge relation is exactly acceptance of pair inputs by three positive OR clauses is bipartite. If all three pairwise clause intersections were nonempty, vertices chosen from those intersections form a triangle. Hence two clauses are disjoint; every edge crosses those clauses, yielding a Boolean 2-colouring. C4-freeness is not needed. Compile exited 0; stdout/stderr saved as pair-three-cnf.* in task scratch.

Read full primary-source Jukna paper via https://eccc.weizmann.ac.il/report/2005/021/download/ on 2026-11-25: counterexamples use saturated extensions, so their triangles exclude direct applicability here. The paper explicitly distinguishes the easy formula lower bounds for C4-free graphs from circuit lower bounds.

### Counterexample update 2026-11-25T02:34:10.897878+00:00

The concrete C5 witness now compiles in Lean: results/orch/lemmas/counterexample_c5.lean (42 lines), proving size7, no triangles/C4, Monotone2, computation, star profile, and nonempty edge ownership. Exact minimum7 already has repository proofs (L_meta_931.coreC5 and L_meta_927.base_C5), so copying that solved lower bound was abandoned. C6 minimum8 likewise already proved in L_meta_4795; redundant running MILP stopped after discovery.

The C5 bad-prefix seven-gate synthesis (OR(0,2), OR(1,3), AND of the two, owning three path edges) is infeasible (HiGHS,2.2 seconds). This rules out that particular stronger-universal counterexample, not all bad minima. Next target: theta graph with paths2,3,3, seven vertices/eight edges, canonical cost11; search ten gates.

## minimal_existence global-surgery obstruction — 2026-11-25T02:35:20.349060+00:00

NEW CHECKED COMPONENT: minimal_two_dirty_obstruction.lean, 72 lines, sha256 d54c6c501dd749d63ae1889b6084cf66e725a205042d1c137da043e9f895382a, lake env lean exit0. On matching {ab,cd}, let g=(a∨c)∧(b∨d), h=(a∨d)∧(b∨c), output g∧h. This seven-gate circuit computes exactly ab∨cd; g and h each own the two disjoint graph edges, while the final sound AND owns none. Every gate is essential even on edge ab. Replacing ANY gate by ANY earlier wire changes the function (`no_earlier_bypass`), yet the direct circuit has three gates. This does not refute the gap: it refutes the route from semantic liveness/maximal soundness/local bypass irreducibility to star ownership. A genuinely global gate-count comparison is necessary. The last dirty gate h is corrected by a sound gate whose other input g is also dirty, so the one-dirty theorem cannot be applied to its suffix in isolation.

### Counterexample stop 2026-11-25T02:37:01.985952+00:00

Root reported lease HTTP410 and instructed immediate stop. Theta233 SAT solver terminated; its complete CNF, stdout, stderr, possible partial solution, and controller output remain in /tmp/oec/pequalnp-pilot-59/counterexample-sat-theta233-k10.*. No theta233 verdict claimed. All scripts and the Lean-compiled C5 ownership witness are preserved under results/orch/lemmas. No further searches started.

## minimal_existence stopped — 2026-11-25T02:37:06.497429+00:00

Root instructed stop mathematical work after HTTP410 lease response. No further proof edits/builds. Completed standalone checked files: minimal_cone.lean (510 lines, max-AND soundness), minimal_two_dirty_obstruction.lean (72 lines, sha256 d54c6c501dd749d63ae1889b6084cf66e725a205042d1c137da043e9f895382a). Both lake env lean exited0, logs empty. Root merged components; combined target validation is root responsibility.

Global analysis: local single-gate surgery cannot suffice (certified obstruction); last dirty AND may be corrected by a sound gate also reading other dirty ancestors, so isolating its suffix destroys graph-function assumptions. Global gate-count comparison remains unresolved. Library global AND-count/cover theorem L_meta_217 only reaches threshold5; larger bounds are graph-specific. L_meta_1006 refutes a boundary-promise bound on an11vertex graph with triangles, not our exact girth5 graph function.

Literature leads discovered via read-only web search2026-11-25: Nets Hawk Katz, On the CNF-complexity of bipartite graphs containing no K2,2s, https://arxiv.org/abs/1206.6068, abstract claims C log d clauses for a bipartite graph with average degree d. Applicability to exact quadratic Boolean functions is UNVERIFIED: graph representation may only match weight-two inputs. Jukna slides https://web.vu.lt/mif/s.jukna/papers/single-dag5.pdf mention C3,C4-free monotone FORMULA lower bounds; no circuit analogue was confirmed. No proof conclusion drawn from these leads.

## Constructive strategy stopped 2026-11-25T02:37:10.211211+00:00
Root reported lease HTTP410 at 02:36 and ordered immediate mathematical stop. Latest matching intrinsic component is checked and root reports named build/push at 923c823. Compact source remains unchanged at 591 lines.

Full-proof exploration: a canonical star-cover circuit would cost |E|+τ(G)−1; the tempting separate OR lower bound |E|−1 is unproved for arbitrary monotone circuits and must not be assumed. Last dirty AND can often be bypassed separately for each sound star-filter reader by absorption, but a shared OR context feeding filters centered on opposite operand sides requires duplication and defeats a local rewrite. Existing L_meta_3760 proves no exactly-one-dirty-AND least circuit for bipartite C4-free graphs (10,039 lines); L_meta_1528 supplies a detailed single-dirty ORsharing count. Extending that count to several dirty gates, or to merely nonstar-owned gates, remains the unresolved route. No complete proof or refutation of L-meta-1031 was found by this strategy.

## pair_normalization pause — 2026-11-25T02:37:10.215280+00:00

Root reported HTTP410; stopped further proof work. Current pair_three_cnf.lean now includes adjacent edge cover classification (a nonempty triangle/C4-free graph pair-represented by three positive clauses is a double-star). Last already-started compile result is recorded in pair-three-cnf.stdout/stderr. Additional unformalized observation for (AB∨Q)C: if Q nonempty, choose q∈Q; q is adjacent to every vertex of C, so triangle-freeness makes C independent. Every graph edge touches C, hence C gives a bipartition. If C singleton, graph is a star. Under C4-free, all vertices outside C except q have degree at most1. No proof coding begun for these observations.
