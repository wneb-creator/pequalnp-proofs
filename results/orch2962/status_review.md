# Independent review for L-meta-2962

The exact assigned statement is the core-cover inequality

`|D| + |T| ≤ |U| + |maximalCores| + |T'|`,

where D is the union of accepted graph edges over maximal cores, U is the union of their full gate cones, T is a minimum cover of G, and T' is a minimum cover after deleting D. Assumptions include a Boolean bipartition, no four-cycle, exact backward binary AND/OR circuit semantics, and an implicant-lift fixed point. Neither least size nor every gate lying in the output cone is assumed.

Definition audit: `Core.maximalCores` and `Core.coneSet` range over all gates, including dead gates. In contrast, the fixed-point condition prevents lifts only in the output cone. Dead core cones can therefore contain implicant-mixing ORs that would be forbidden in the output cone. This is a possible counterexample avenue, not an established refutation.

Accepted nearby refutations do not immediately settle this statement. L2969 uses two shared-cone copies of an edge core, one unread, to refute a companion total-size accounting inequality; the present inequality has ample slack there. L3446 refutes a variant counting only a filtered portion of U, with D of size two, cover size three, residual cover size two; the full U has five gates and one maximal core, so the present inequality reads 5 ≤ 8. L3444 and L3762 provide additional finite lift-fixed seed circuits for exact search. Their graph/circuit definitions have been sent to the search agent.

No immediate flaw or concrete counterexample to the exact assigned inequality has been established by this review.

## Checked components

`lemmas/SemanticCore.lean`: 199 lines, 8,114 bytes, SHA256 `835a5879cddf2e8281269246758e72146b597181dab77d9399598e04d539c46d`. The copied evaluation prefix exactly matches L3657 from `step` through `cval_gate`. New proofs establish that every valid AO2 wire is true at the all-true input, a wire below the graph function cannot be a raw input, and therefore each core is an AND gate with an operand not below the graph function. AO2 backward-read and exact-binary assumptions are used explicitly; no minimality, output-cone, bipartition, or fixed-point assumption is smuggled in. These claims also apply to dead cores. Confirmed build exit zero; stdout has a simp suggestion and a deprecation warning, stderr is empty.

`lemmas/CombinatorialCover.lean`: 76 lines, 3,196 bytes, SHA256 `3f618007e59b11aa8a4518aa000af6e295283fcf30e51f4de0a529519adf7d7f`. Covers of deleted and residual edges combine by union. A minimum-cover cardinality then gives the stated conditional budget inequality. The relative variant needs to cover only deleted edges whose endpoints both lie outside the residual cover. Residual minimality and D being a subset of graph edges are not assumed or needed; the hypotheses are stronger where appropriate. The crucial `D.card + S.card ≤ budget` is an explicit premise, not an established circuit fact. Confirmed build exit zero with both `2962-combinatorial-cover2.*` logs empty.

Both components pass official plain/import/namespace parsing after an in-memory parser-only trivial final theorem is appended. That sentinel is neither written nor compiled and is not a proof claim. Independent preservation verdict: PASS for both partial components. Neither proves the full assigned inequality.

## Other already-implied public statements

Read-only feasibility check: open L-meta-2151 and L-meta-2159 each follow directly from accepted L-meta-4033, which excludes any size-at-most-15 FanInTwo circuit for the exact nine-vertex Petersen edge function. Their additional first-wire, second-OR, or no-NOT assumptions are unnecessary. Assuming size below 16 supplies the forbidden `HasCircuitSize` witness. Exact public formal statements are cached in `audit-candidate-2151.json` and `audit-candidate-2159.json` under task scratch. No unleased proof edit or build was made for them.
