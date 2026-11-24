L-meta-2215 orchestration

Lease obtained 2026-11-24T17:56:23Z. Root alone holds and renews lease.
Task: find 61-gate monotone circuit for 12-point/13-line subplane graph, with conditional extra wire, or submit useful reduction after real effort.
Naive 12 point stars cost 59 gates; desired four-line OR costs 3 more, yielding 62. Need one-gate saving.
Strategies: circuit_search computational construction; structural_strategy factorization and conditional sharing; checker_review independent compliance; lean_setup toolchain recovery.
L-meta-1035 is still posted, has zero open PRs in desk feed; not assigned to us, so no work on it.

Structural strategy: use full-plane coordinates p=actual point index+1, l=actual line index-12. Then near(p,l) is (p+l)%13 in D={0,1,3,9}; point0 is absent and D is exactly the auxiliary line set. Geometry (all independent rectangles have min cardinality ≤3) was checked by enumerating all8192 point subsets; no violations. The deleted-point graph has 553 maximal independent rectangles. A symmetric vector maps Fin25 points through +1, lines through -12, allowing a compact hSearch. Auxiliary-negative boundary vectors remove D from their line coordinates.

Wire monotonicity: draft in results/orch/lemmas/WireMono.lean proves every wire true-preserving for arbitrary Fin n inputs under Monotone2. Adapted the checked fold induction from R_meta_650_713; initial List.ofFn monotonicity is direct. Awaiting toolchain/cache readiness before compilation.

Circuit search 2026-11-24T17:59:59.734992+00:00: complete monotone boundary basis uses48 edge-positive rows,553 maximal-independent negative rows; auxiliary uses4 singleton positives,197 maximal-independent negatives after deleting auxiliary lines. A 61-gate near miss has F output82,Q output85 and only failed edge support{7,13}; this is baseline missing one edge. Data and diagnostics are in /tmp/oec/pequalnp-pilot-37/circuit_search/. Computational search remains active.

Root drafted R_meta_2215_37, not yet compiled or submitted. It splits into four-point geometry (715 finite cases) and monotone boundary synthesis, and locally proves all-wire monotonicity. Direct search still active. Existing R_meta_2215_317 by Timothy Tamm deletes three stars; our route is distinct.

Geometry Lean checkpoint: results/orch/lemmas/Geometry.lean compiled successfully via lake env lean, proving four_points by decide +kernel and full rectangles using Finset.exists_subset_card_eq. Full stdout/stderr log is scratch/structural_strategy/geometry-direct-build.log (empty on success). A faster combinatorial proof using13 degree checks and169 pair-intersection checks is also being tested.

2026-11-24T18:03:40.402802+00:00 WireMono compiled successfully with pinned Lean 4.36.0 via lake env lean; exit 0, no output or warnings. It generalizes to all n and all wire indices, not only the distinguished circuit output. Source: results/orch/lemmas/WireMono.lean; complete log: /tmp/oec/pequalnp-pilot-37/wiremono-build.log.

Circuit search 2026-11-24T18:06:11.323276+00:00: early/interleaved auxiliary seed also reaches61 gates with exactly one missing edge{0,20}; F wire85,Q wire54. Exhaustive single-gate repair checked206790 substitutions (either op, arbitrary earlier binary fanin, outputs reselected): no improvement;64 score1 substitutions. Full diagnostics stay in scratch/circuit_search/exhaust.log. Two stochastic searches remain active, finishing roughly18:18 and18:20 UTC.
