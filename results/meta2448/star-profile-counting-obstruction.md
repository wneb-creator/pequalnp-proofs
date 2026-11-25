# Star profile and the proposed counting bound

Read-only repository and mathematical investigation by proof_routes, 2026-11-25. This note does not claim a proof or refutation of L-meta-2448.

## Input copies remove the profile restriction from an OR-only claim

Start with any backward-reading AND/OR circuit C with no nullary AND gates. For each original input x_v prepend one gate q_v = AND[x_v], or equivalently AND[x_v,x_v]. Replace every original input reference by q_v; shift the original gate references by the number n of copies. Retain the shifted output (or its copied input, if the output was an input).

The resulting circuit D has exactly the same function and OR count as C and exactly n more AND gates. It is still Monotone2, including with the binary idempotent form. It has HasStarProfile for every simple graph G, regardless of what function C computes:

- Each copy q_v owns precisely the graph edges incident to v, since it has no earlier gate in its cone and is true exactly when x_v is true.
- Every later AND gate that is true on an edge input has a true input copy in its strict cone. Descend through a true operand at each gate; every AND has at least one operand, every true OR has a true operand, and strict backward reads make the descent end at an original input. That input is one of the edge endpoints. The corresponding q_v is an earlier true AND in the cone, so the later gate owns no graph edge.

The no-nullary-AND condition is deliberate: a constant-true AND with no inputs has no true input ancestor. Ordinary proper binary circuits already satisfy the condition. If a separate constant-elimination normalization is available, it extends the observation to arbitrary nonconstant circuits; no such normalization is silently assumed here.

Therefore an OR-count inequality of the form

    exact graph function + HasStarProfile -> OR_count >= |E|-1

would already imply the same inequality for every proper backward-reading circuit for the exact graph function, with no profile assumption. The profile itself cannot provide the missing OR-only accounting. This observation is NOT a counterexample to that inequality, and does NOT transfer the proposed TOTAL-size lower bound, because D has n extra AND gates. The copies are semantically redundant, so D is generally not minimum; the observation likewise does not refute a theorem restricted to minimum star-profile circuits.

## What the accepted repository actually supplies

A census of accepted L_meta files found no occurrence of HasStarProfile outside the current local L_meta_2448 partial. Relevant weaker or stronger results are:

- L_meta_1599: exact graph computation by AND/OR circuits implies EveryEdgeOwned. Together with a star profile, choosing one center for each nonempty owning AND gives a vertex cover of cardinality at most the number of AND gates. This is the sound elementary AND-count half; no independent OR-count half follows from it.
- L_meta_1407: the desired |E| + |T| <= gate_count+1 conclusion when EVERY AND is globally graph-sound. This is a genuine accepted theorem, not merely the conditional wrappers L_meta_1601/1602.
- L_meta_4767: the same total-size conclusion under a slightly weaker gatewise condition: each AND is globally graph-sound OR accepts at most one graph edge in total. This concerns all accepted graph edges, not only the edges it owns. A star profile does not supply this premise.
- L_meta_599 and L_meta_4837: OR_count >= |E|-1 for graphs with no four-cycle and the additional condition that every induced subgraph has at most as many edges as vertices. Thus these cover pseudoforests, but not Petersen, the adjacent-deletion core (10 edges on8 vertices), or theta graphs with more than one independent cycle.
- L_meta_1491/L_meta_4183: size accounting in least TopForm with an uncovered-edge correction Ustar. A star profile has not been shown to eliminate that correction.

## Remaining precise obligation

For a minimum star-profile circuit, one would need a new exchange or charging argument for an AND that owns a star but also accepts other graph edges through earlier true AND gates, or accepts nonedge pairs/singletons that later gates clean up. The ownership premise only controls the first category of newly owned edges, while the accepted counting proofs use stronger information about all values of a gate. Neither minimum total size nor HasStarProfile alone has been shown here to bridge that distinction.

A candidate smaller circuit is therefore not yet a refutation of the posted existential minimum-star statement merely because it beats the canonical |E|+tau-1 construction. One must additionally establish a matching lower bound for star-profile circuits, or independently certify that all circuits at that smaller size fail the profile. No general bound of that strength was established in this investigation.
