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
