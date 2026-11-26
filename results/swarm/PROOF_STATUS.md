L-meta-4970 proof status

The posted theorem is not proved or refuted. These files are checked partial work, not a submission of the full gap.

The established AND half

OrdinaryAnd.lean proves that the original AO2, C4-free, exact circuitFun, and zero mixed OR-reach hypotheses imply an ordinary vertex cover S with S.card at most the number of actual AND gates. The serving-witness hypothesis is not needed for this half.

For each matching edge, compare its positive pair assignment with a maximal non-neighbor assignment on each palette. Each comparison gives an AND operand slot whose raw OR reach contains the endpoint and stays within the opposite endpoint neighborhood. Same-palette slot collisions contradict C4-freeness; opposite-palette collisions contradict zero mixing. Two slots per matching edge inject into the two slots of each AND gate. The inlined Konig proof converts the matching bound into the cover.

The same file proves the exact AND/OR partition of circuit size. Its last conditional lemma explicitly retains E.card <= OR-count + 1. Proving that premise would finish the posted theorem; it is not currently established.

The witness forest

Independent root review and compilation of helper-3 commit c69a0313823ca80db1b5968e71213ea32c75cdac passed. Its chosen_productive_family_forest gives distinct actual OR labels on an acyclic graph, and chosen_productive_family_overlap_budget gives |labels| + cc = |edges| after the appropriate witness-family parameterization. Here cc means overlap of witness components, not connected components of the original graph.

The interface requires finite connected families of safe witness supports, pairwise intersections of size at most one, and embeddings into the original edge set. The graph-specific family construction still needs to be assembled. The selected productive OR gates need not be pure disjunctions, live, or below the output. Their nonempty support conditions are semantic singleton support, not syntactic OR reach.

The remaining count

With a chosen OR basis L of size |E|-k and maximum matching size tau, the missing joint inequality is:

    k - 1 <= |OR gates outside L| + (AND count - tau).

The checked matching injection leaves exactly 2*(AND count - tau) unused AND operand slots. Counting how the witness components connect through the remaining gates is unresolved. FlagComponents.lean checks the local C4-free flag and unique-owner facts; it does not establish this global inequality.

Important failed shortcuts

- A cover restricted to available witness centers can exceed the AND count.
- Counting only semantically pure OR gates and OR gates below the output is insufficient, even on a tight circuit.
- The number of pure-witness components can exceed the AND count.
- A single independent-set baseline need not provide enough disjoint samples for all witness components.
- A subfunction below the target can reach too many witness components for a local residual bound. Even exact full-output computation does not suffice for an unqualified matrix/rainbow-forest bound when nonstar pure sources are allowed.
- Counting semantic bad OR gates alone does not pay for all witness components, even after edge-active and no-safe-AND-below-AND normalization.

INTERMEDIATE_COUNTEREXAMPLES.md records the first independently checked constructions published on this branch. MATRIX_OBSTRUCTION.md and MatrixObstruction.py reproduce a larger exact-output obstruction to the unqualified matrix and semantic bad-OR bounds; the posted conclusion holds on that circuit. Other scoped obstructions and complete diagnostics are retained in scratch and on the helper branches. None is a refutation of the posted statement.

Finite and stochastic searches

Helper searches have excluded many finite graph/circuit cases but do not constitute a universal proof. Root stochastic searches use exact monotone test sets (edge positives and maximal-independent negatives), singleton/complement tests for actual pure-OR witnesses, and explicit syntactic mixed-reach evaluation. Known 24-gate K5-incidence and 35-gate affine constructions pass the controls. All four longer runs completed without a valid smaller circuit. Their final candidates each fail one edge input and one serving witness; SEARCH_RESULTS.json records seeds, requested durations, iteration counts, source hashes, and independently re-evaluated outcomes. Failure of a heuristic search is not an exclusion.

The live desk row was rechecked on 2026-11-26 and its statement is unchanged. A heartbeat at 00:25 UTC returned HTTP 410 and was reported to the coordinator. No new lease was requested. No FINAL was posted, no PR was opened, and the desk lease was not released.
