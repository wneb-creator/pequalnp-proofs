# L-meta-2448 research checkpoint

The posted theorem remains unproved and unrefuted. Do not submit this branch as a proof PR: the named Lean file contains checked helper declarations but no declaration proving the posted statement. Research artifacts are preserved on the fork branch pnp/pilot-74; a future proof PR must have a one-file net diff.

The exact task statement is in statement_2448.txt. It asks for a minimum monotone circuit with star ownership for every triangle-free, four-cycle-free finite graph. Root held only this lease after the earlier L-meta-1896 lease failed with HTTP410; DESK_DIAGNOSTIC.txt preserves that response. No other pilot lease was released.

## Checked mathematical components

- A minimum monotone circuit exists. Any minimum has an equal-size minimum replacement with backward references and exactly two AND/OR operands, including the empty-graph case.
- Pairwise-intersecting owned edges have a common center under the graph hypotheses. Pair-clean AND gates therefore suffice for star ownership.
- Downward monotone rewrites preserving all graph-edge pairs preserve the exact graph function. A forced-false gate can be deleted safely even with forward references. Every gate of a minimum exact circuit consequently has a pivotal edge.
- A unique pivotal edge permits a same-size replacement by its input AND. Two singleton-positive inputs covering all pivotal edges permit replacement by their OR. A suitable common pivotal center permits operand restriction.
- An isolated matching block can be replaced by two edge ANDs and an OR with the same three-gate budget, retaining all shared support ORs. A more general semantic repair allows arbitrary outside readers, provided the replacements are clean, jointly cover the old active graph pairs, and their new union reaches the output.
- Four distinct endpoints of two disjoint edges induce only a matching or one of four paths. Checked Boolean choices supply clean replacement stars for these cases.
- The vertex-cover construction gives a star-profile circuit of size at most the edge count plus cover size minus one. The matching universal lower bound is NOT proved.

## Obstacles and negative controls

A checked eight-vertex, ten-edge example computes the exact graph function using seven ANDs and eight ORs. Thus the proposed unrestricted OR-count lower bound of edge-count minus one is false. That circuit is not minimum and does not refute the posted statement.

A checked five-cycle circuit has star ownership while one gate has pivotal edges with no common center. Owned and pivotal edges cannot be identified. A twelve-vertex extension of the shared-support example attains the standard nineteen-gate upper bound with bad ownership, but its minimum status is UNVERIFIED; it is not a refutation of the existential theorem.

The remaining obstacle is an unbounded component argument. Larger CNF blocks and mixed OR signals are not covered by the four-vertex exchange. Closing components through shared support can add clean, empty-owning AND gates. These may pay for replacement OR joins, but no total cost bound has been proved. One possible reconstruction forces a whole component false, prunes zero/copy gates, and appends a star circuit for the lost graph edges; its required cost inequality is still open. Minimizing AND count among size-minimal circuits may be a better secondary measure than preserving an initial good prefix.

Finite SAT searches and random sparse CNF probes found no counterexample. Their UNSAT results are not Lean-certified; timeouts are UNKNOWN. The checked finite witnesses use ordinary kernel-checked decide. Search scripts, complete batch logs, and hash manifests are preserved separately.

Primary literature found during this job supplies single-level bounds, not the needed unrestricted-circuit normalization. Detailed access limits and explicitly unverified claims are recorded in STAR_RESEARCH.md and STAR_LIBRARY.md.

## Validation and continuation

VALIDATION.txt and TIMELINE.md record exact build, review, checkpoint, and checker outcomes. Every newly compiled component was independently reviewed before a fork checkpoint. The full posted theorem has never been claimed. The checker setup attempt reached a missing dependency object fault; no accepted checker verdict exists. The working targeted cache was restored and byte-verified after the bounded full-cache experiment.

Local build environment uses Lean4.36.0 and the repository-pinned Mathlib. No project configuration was changed. The standard source file is lean/PEqualNP/Outside/L_meta_2448.lean. Helpers are independently available in results/orch/lemmas, and final integration preserves their bodies under permitted namespaces.

Final integration:4450 lines, buildexit0 and23-key axiom audit with standardaxioms only. Actual sourceguard rejects only the absent posted theorem after the identifier-format correction. Full localchecker still faults on missing full Mathlib cache. The concrete RectangleRepair and separate IsAO2 model lemma are checked under their stated reachability/support assumptions; DoubleStarGeometry does not by itself prove the stronger arbitrary-reader coverage requirement.

Lease closure: the root renewal timer was stopped, then only L-meta-2448 was released with reason other after the full checked checkpoint was pushed. No PR was opened. The full task remains unproved and unrefuted; this handoff preserves partial results only.
