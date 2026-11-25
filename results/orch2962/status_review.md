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

`lemmas/StructuralCones.lean`: 244 lines, 10,732 bytes, SHA256 `257f0462ac13a4c1ea4b55b0975d8e3dca1301a14d46f3d4044e266897f4721e`. Its cone-support block exactly matches L3700. New proofs show maximal cores form an antichain, a maximal core belongs to another maximal core's cone only when equal, every core reaches a maximal core, and the union of all core cones equals the union of maximal-core cones. The finite-maximum argument uses the strict increase of gate indices along `InCone`, so no unstated circuit assumption is needed. `fixed_live_or_below` explicitly requires the OR gate to lie in the output cone; it correctly makes no claim about dead mixing gates. Confirmed build exit zero with both `2962-structural-cones2.*` logs empty; official parser checks pass. Independent preservation verdict: PASS for this structural component.

`lemmas/CountingExamples.lean`: 54 lines, 2,236 bytes, SHA256 `2031a5b55faebc9f62ca0f5d19d0dd7575ace1273dd1ffba766966c3df82937d`. Kernel decisions certify a K2 circuit consisting of `x0 AND x1`, then its result AND x0. The second gate is a maximal core with one implicant operand, both gates form U, D is the single graph edge, and the posted inequality has margin exactly one. Thus this is a verified definition/counting example, not a refutation. Successful logs are empty; official parser checks pass. Verdict: PASS.

`lemmas/StructuralPorts.lean`: 294 lines, 13,417 bytes, SHA256 `53345c0df7eff215701b184cddb71bcdc5b8e90c1c76ed02b21b745977ba4e68`. The prefix is the exact frozen cone component. Every nonmaximal gate in U has an internal reader port; the image of internal ports therefore covers U minus maximal cores. Combining that cardinality with two ports per gate gives at most `|U|+|maximalCores|` primary-input ports. This is a syntactic port count only; no edge/cover charge into those ports is claimed. Confirmed successful logs are empty; official parser checks pass. Verdict: PASS for preservation.

## Other already-implied public statements

Read-only feasibility check: open L-meta-2151 and L-meta-2159 each follow directly from accepted L-meta-4033, which excludes any size-at-most-15 FanInTwo circuit for the exact nine-vertex Petersen edge function. Their additional first-wire, second-OR, or no-NOT assumptions are unnecessary. Assuming size below 16 supplies the forbidden `HasCircuitSize` witness. Exact public formal statements are cached in `audit-candidate-2151.json` and `audit-candidate-2159.json` under task scratch. No unleased proof edit or build was made for them.

L4033 passes current official plain/import/namespace checks. Its helper prefix is 520,667 bytes, and the exact L2151 statement is 1,113 bytes; even 2,000 bytes of declaration/proof overhead would total 523,780 bytes, below 524,288. However, four custom structures in L4033 trigger CONTRIBUTING rule 5: such a file waits for a person to read it rather than automatic merging. This is a review-routing caveat, not a guard rejection. No custom-type conversion was attempted for an unleased target.
