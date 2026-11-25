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
