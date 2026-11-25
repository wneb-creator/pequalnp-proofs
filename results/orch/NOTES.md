# L-meta-1770 orchestration notes

Only root holds the lease and submits. Append findings with strategy names and UTC timestamps. Scratch Lean attempts belong in results/orch/lemmas; root owns the final Outside file.

Lease acquired 2026-11-25T02:59:42.485Z; original expiry 03:19:42.485Z.

## Structural strategy 2026-11-25T03:02:53.695440+00:00

- Existing R_meta_1770_401 proves bottom-bottom double-junk case with constant 204; leaves bottom-deep/deep-deep. R_meta_1770_1 splits singleton/quadratic behavior. L_meta_3807 solves non-nested junk globally.
- Existing leastness infrastructure (1495 no duplicate gates; 1498 tree of below-F gates; 1499/1501 normalize below-F AND nesting) does not remove dirty AND nesting.
- New scratch Structural.lean proves semantic separation: junk gates OR-reaching opposite sides of a top have incomparable truth functions, witnessed on graph-negative assignments. It uses only IsAO2 and top/junk definitions. Initial Lean attempt awaits PEqualNP.Defs oleans.
- Remaining possible route: every nested opposite-junk pair must have mixed AND/OR paths, since pure OR reach would force comparable truth functions and violate semantic separation. Need an amortized charge to such mixed paths; no linear bound established yet.

## Reduction design 2026-11-25T03:04:00.195995+00:00

Existing cuts partition singleton-vs-quadratic witnesses, and bottom-vs-deep junk. New candidate reduces exact residual edge graph to its minimum-degree-three core. Premise 1 is already checked support bound (L_meta_2074). Premise 2 bounds arbitrary core subgraphs of the exact full target predicate, with original graph and circuit fixed. Degree-one/two peeling costs at most twice the original support, giving coefficient k+2. Full target restrictions retained; core source currently 1370 characters, under the 2000 printed-character screen pending checker. Candidate: results/orch/lemmas/Reduction.lean.

## lemma_search 2026-11-25T03:04:24.867905+00:00

- Repository search found no checked general bottom-deep or deep-deep bound. Existing `R_meta_1770_401` proves bottom-bottom with constant 204; `L_meta_3807` covers junk antichains. `L_meta_5242` covers only two nested junk plus a non-concentration assumption.
- `L_meta_2074` (222 lines) proves the useful support bound `IsLeastAO G C → G.support.ncard ≤ C.size+1`.
- Compiled `results/orch/lemmas/LemmaSearch.lean` with Mathlib only: general 3-core peeling plus `bound_of_core` for arbitrary edge subset T. Low-degree peeling removes at most 2*support(G) edges. Both compile with exit 0; complete build output is `/tmp/oec/pequalnp-pilot-63/lemma-search-build.log` (empty on success).
- `reduction_design` is integrating this into exact L-meta-1770 reduction. Its two independent children are the known support bound and the target restricted to subgraphs whose nonisolated vertices all have degree at least three.
