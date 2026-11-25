# L-meta-2583 independent mathematical assessment

This is a research note, not a checked Lean proof or a solution of the posted gap.

## Exact semantics

`TopForm.IsAO2 n C` means AND/OR only, exactly two operands per gate, and only backward reads. There are no constant gates. `ReadK.IsReadK n C 1` means that every prime implicant has **one jointly bounded proof tree** reading each of its variables at most once. It does not restrict global fanout. Scalar minimum reads taken separately for the two variables are insufficient.

For the incidence target every prime implicant is an incident point-line pair. A read-1 tree of such a pair therefore has exactly two leaves and exactly one AND gate; every other gate occurrence is OR. This is stronger than merely having some lowest AND joining the pair.

## What a successful normalization would imply

Let the bipartite incidence graph have m edges and minimum vertex cover size tau. For a C4-free bipartite graph, the natural read-1 optimum is m + tau - 1. The following is an informal proof outline that still needs formalization:

1. Inspect the OR closure above the output. Every wire in that closure is below the target and cannot have a linear monomial, since the target rejects every singleton.
2. For each AND in this output OR closure, replace each operand by its OR-only input part, deleting the AND branches below that operand. Delete empty products and bypass unary ORs. Read-1 supplies every target edge through one of the retained products. No retained product can add a nonedge, since it is bounded by the original gate and reaches the output through ORs.
3. This pruning need not duplicate a wire: an OR-only operand wire with a nonempty linear part cannot also lie in the output OR closure, by the singleton argument. Thus the output layer and the leaf OR layer are disjoint.
4. Each retained product is an edge rectangle. Its two supports are disjoint, and C4-freeness makes at least one side a singleton. Thus the product is a star. An OR wire with at least two distinct leaf inputs cannot feed stars with distinct centres: those centres would have two common neighbors. OR wires with one-element support can be bypassed to the raw input.
5. Suppose t top ANDs remain. Assign a centre to each star. Their centres cover every edge, so t >= tau. Let t_c count stars assigned centre c and let d_c count their distinct covered neighbours. Their private leaf-OR subnetwork requires at least d_c - t_c OR gates: a binary DAG with d_c distinct raw sources and at most t_c designated sinks has at least d_c - t_c combining vertices. Summing gives at least m - t leaf-OR gates. The output OR network requires at least t - 1 OR gates. Counting the t ANDs gives at least m + t - 1 >= m + tau - 1 gates. Negative lower bounds for individual groups cause no problem.
6. Conversely, partition edges among the centres of a minimum vertex cover and make one star per nonempty centre. Each star of degree d costs d gates (d-1 ORs and one AND), and joining the stars costs tau-1 gates, attaining m+tau-1. Empty centres can be removed.

For the posted incidence hypotheses, line size is q+1. Counting the pairs involving a fixed point through their unique joining line gives point degree q+1 as well, because q*r = N-1 = q*(q+1) and q >= 2. The bipartite graph is regular with N vertices on each side and has no C4. Hall counting gives a perfect matching, so tau=N. Therefore m=N*(q+1), and the read-1 target cost is N*(q+2)-1.

Consequently, the posted normalization is effectively an exact unrestricted monotone AO2 lower bound at the line-star construction. It is not an immediate consequence of Boolean idempotence or semantic quadratic degree. An arbitrary circuit can realize a quadratic prime implicant only through a tree with repeated leaves, so formal polynomial degree-two truncation can erase required edges.

## Small checks and obstructions

A short Python test constructed Fano incidence from the seven nonzero vectors in GF(2)^3, with incidence given by dot product zero. It checked 21 edges, degree 3, and a unique common line for every pair of points. Exhausting all 2^14 vertex subsets gives minimum cover 7; the only minimum covers are the entire point side and the entire line side. Thus the canonical read-1 size is 27. The counterexample agent reports the repository already contains a checked unrestricted Fano lower bound of 27 (L_meta_971); this review did not independently inspect that theorem.

A nonstar block can remain after every below-target internal wire has been lifted. The seven-gate formula

    ((a OR b) AND (c OR d)) AND ((a OR c) AND (b OR d))

computes the matching `(a AND d) OR (b AND c)`. A truth-table check verified that all six internal gates are not below this target, while the final gate is below it. The block has no read-1 edge proof: each accepted pair occurs through at least two ANDs. A direct read-1 circuit costs three gates, so this is not a counterexample to the desired size comparison. It does refute the shortcut that a lift fixed point already has only star blocks.

The lower-bound agent separately reports checked counterexamples L_meta_3444/L_meta_3446/L_meta_2969 to natural cone-budget inequalities, even with bipartiteness, no C4, and lift fixed point. Those examples are nonminimal. Therefore any new block-cost argument must use genuine leastness or a sufficiently strong irredundancy invariant; fixed point plus output connectedness is not enough.

## Current conclusion

No semantic loophole or counterexample to L-meta-2583 was found. The read-1 side has a clear star interpretation and exact expected cost; the unresolved step remains excluding a smaller least circuit that obtains some edges only via repeated leaves in dirty blocks. Existing q=2 evidence motivates q=3 as the next counterexample search (target read-1 size 64), but absence of a search witness would not establish the universal result.
