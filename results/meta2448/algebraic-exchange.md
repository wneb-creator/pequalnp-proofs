# Algebraic exchange investigation for L-meta-2448

algebraic_witness, 2026-11-25. This note records mathematical observations and unresolved steps; it is not a proof of the posted theorem.

The objective now minimizes total Circuit.size, unlike the previous gap's OR-only budget. The output is the exact graph edge function. The graph is triangle-free and C4-free. Existing results already supply a minimum circuit (L_meta_2666), an edge on which each minimum-circuit AND is essential (L_meta_2668), and a star-profile conclusion for pair-sound AND gates (the team's strengthened L_meta_1600 checkpoint).

The remaining normalization problem is to remove nonstar owners without increasing total size. Ownership counts all graph edges on which an AND fires before any true AND in its strict cone. It is not restricted to edges for which that gate is essential at the output. Thus an incidental owned edge can obstruct the profile even when another branch already computes that edge.

For an owned edge, each operand of the owning AND has an OR-only route from one endpoint. Two disjoint owned edges therefore expose a product-like pattern. Pair soundness plus C4-freeness would immediately force a star, so any nonstar owner has an intermediate false positive of weight at most two. This is the useful precise obstruction; no higher-degree witness is needed at the offending AND itself.

A local path example illustrates the potential exchange. For edges ab, bc, cd,

    (a OR c) AND (b OR d) AND (b OR c)
      = (a AND b) OR (b AND c) OR (c AND d).

The product-and-filter realization has three ORs and two ANDs, hence five gates. The star realization

    b AND (a OR c) OR (c AND d)

has two ORs and two ANDs, hence four gates. In a triangle-free/C4-free ambient graph, none of the three linear OR supports can simply be shared by a new two-edge star: {a,c} already has common neighbor b, {b,d} already has common neighbor c, and {b,c} is an edge. Such sharing would create a C4 or a triangle. This observation does not yet exclude sharing through later nonlinear filters.

Reassociation also preserves cost along an AND chain:

    (A AND B) AND C = A AND (B AND C).

If C already contains a true AND on an accepted edge, the reassociated gates do not own that edge; ownership is witnessed inside C's cone. A shared occurrence of A AND B elsewhere must still be accounted for before treating this as a whole-circuit move.

An intervening OR is the main obstruction. Distributing

    ((A AND B) OR R) AND C

generally adds an AND. Under the additional pointwise assumption R <= C, it equals

    (A AND B AND C) OR R,

which has the same two ANDs and one OR as the original fragment. For a final exact output F, the premise follows if R is globally sound: R <= F and F = ((A AND B) OR R) AND C imply R <= C. It does not follow for arbitrary linear or unsound side branches, nor for an internal fragment merely known to occur in the output cone.

Exact graph correctness gives a useful semantic deletion principle: a monotone modification that only decreases the output and preserves every edge input preserves the whole function. However, this does not authorize a gate replacement just because one selected edge remains accepted; all edge inputs on which the gate is essential must be retained.

No applicable primary theorem establishing the general size formula |E| + vertexCoverNumber(G) - 1 was found in allowed-host literature searches. That formula and a global AND-sound normalization remain unverified here. The existing R_meta_2448_17 reduction leaves an owned-edge cross-adjacency condition and a prefix star-exchange condition as hypotheses; it must not be treated as an unconditional proof.

## Checked classification of shared linear cleanup

The119-line component `checked/linear-cleanup.lean` checked on2026-11-25, with complete output in `validation/linear-cleanup-003.log` (exit0). It uses propositional valuations and generic SimpleGraph sets; it is not a Circuit rewrite.

Let A,B be disjoint literal supports, each containing at least two vertices, and let g=OR(A) AND OR(B). For any linear context T whose cleanup h=g AND OR(T) is correct on all pairs, decrease h to

    h' = [OR(A intersect T) AND OR(B)]
         OR [OR(B intersect T) AND OR(A)].

The component proves h' implies h pointwise and h'=h on every pair input. Moreover A intersect T consists of vertices adjacent to every vertex of B; likewise B intersect T consists of vertices adjacent to every vertex of A. C4-freeness makes each of these two fixed center sets a singleton or empty, independently of T. Therefore every reduced cleanup is zero, one fixed left-centered star, one fixed right-centered star, or their union. The reduced functions are globally graph-sound, even though the premise required only pair soundness.

An unformalized circuit consequence covers a bounded sharing pattern: if g has r>=2 immediate consumers, all being these linear cleanup ANDs, then replacing g and its r consumers by at most two centered ANDs and their OR uses at most3 gates, while deleting at least r+1>=3. The original OR context wires can remain for other consumers. Every replaced output decreases and preserves graph-edge inputs, so the previously checked EdgePruning semantic principle preserves the final exact graph function. There is still a syntactic obligation to retime/reindex the replacement DAG, since an early cleanup may need the union before a later old consumer's slot. Both new star ANDs depend only on inputs already available at g, so this is a topological bookkeeping issue in the restricted pattern, not an established Lean theorem.

For one cleanup consumer, replacing g plus that consumer gives only two deleted gates. A third slot is available when its context OR is private; this is the private P4 exchange. If that OR is shared, the three-gate replacement can increase size. Arbitrary nonlinear consumers, operands containing previous ANDs, and the one-use shared-context case remain unresolved. Nothing here proves that every minimum circuit has the restricted linear pattern.

## Two centers and arbitrary contexts

Suppose the pure product's two universal centers c in A and d in B both exist. Every graph edge a-b across A and B then has a=c or b=d: any exception gives the C4 c-b-a-d-c. Consequently the two-star function H=c AND OR(B) OR d AND OR(A) is globally graph-sound, implies the product, and agrees with it on every graph-edge pair. Triangle-freeness also implies A and B are disjoint, since any intersection vertex would make a triangle with c,d.

For an arbitrary monotone output context, write its Boolean cofactor decomposition as F=R OR (g AND K), with R the output when g is set false. Then F=R OR H. Proof: the new expression is below the graph function, and any accepted graph-edge pair is already accepted by R or else is accepted by g and therefore by H. Monotonicity of R and H extends equality from edge pairs to all graph-positive inputs. `TwoCenterRepair.lean` formalizes this semantic assertion with the decomposition and monotonicity assumptions explicit. It does not construct the cofactor circuit or prove a size bound.

A concrete unformalized budget applies when g has at least three distinct immediate readers: setting g=false deletes g, makes each immediate AND reader false, and bypasses each immediate OR reader to its other operand. Deleting those at least four gates pays for H's three gates and the final OR with R. All A/B predecessor wires remain available. Further constant propagation can only help. This is a DAG-level substitution argument; an ordered-list construction is still required.

Deleting g can increase ownership at remaining later AND gates, because ownership considers all earlier true ANDs in the strict cone. Thus this is not an all-gates ownership-preserving exchange. Two potential secondary orders avoid that unsupported claim: (1) total true entries on nonedge-pair inputs over all AND gates strictly decreases when the removed product is pair-dirty, because old gates only decrease and H is sound; (2) if g is the first nonstar gate, insert H's two sound ANDs immediately after the old A/B predecessors at g's position, preserving the earlier good prefix and moving any remaining first bad gate later. Neither secondary-order argument supplies the missing existence of the required two-center pure product.

The precise nonlinear obstruction is visible from K: any pure-A independent set accepted by K must dominate every vertex in B, or adding an undominated b would produce an independent input accepted by gK. Such dominating sets can have degree greater than one; they are not captured by the two singleton centers. The full exchange must handle these contexts, products with only one or no universal center, and products whose operands contain earlier ANDs.
