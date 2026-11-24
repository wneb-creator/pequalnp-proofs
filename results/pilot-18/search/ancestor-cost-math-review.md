# Partial-edge cost on the exact ancestor cone

Verdict: PASS, conditional on the reviewed partial-edge cost theorem and an
ancestor encoding that does not undercount dependencies. The intended exact
encoding makes a[g,h] true exactly when prefix gate h is an ancestor of g.

Prune every gate outside g's dependency cone and renumber the retained gates.
The output function, singleton support, and accepted edge rows are unchanged.
Every retained AND still computes its old function and is clean for the
ambient graph. The pruned circuit has

    m = 1 + sum(h < g) a[g,h]

gates, counting g itself. Apply the partial-edge theorem to that circuit.
For proper support S and residual accepted graph H,

    |S| + |E(H)| + tau(H) <= m+1 = 2 + sum(h < g) a[g,h].

With existential cover bits c, q bits for H, and g possible strict ancestors,
this is exactly the signed cardinality condition

    sum(S) + sum(q) + sum(c) + sum(h < g) NOT a[g,h] <= g+2.

The right hand side is g+2, not g+1. Full singleton support remains exempt
because the augmented model has free TRUE. As before, the edge-cover clauses
may remain unconditional because full support makes every q bit false.

An exact ancestor model gives the stated condition. A permitted overestimate
of the ancestor count would weaken it and still preserve UNSAT completeness,
but an underestimate can incorrectly exclude real circuits. Actual directed
reachability, repeated operands and all source-wire cases must be handled by
the encoding. Structural reachability is sufficient; semantic irredundancy
is neither required nor assumed.

For a full-edge wire of proper support and lower bound 17, the strengthened
cut requires all sixteen earlier gates to be ancestors. If another full-edge
wire of incomparable support occupies the immediately preceding slot, it
cannot be an operand of the final OR, and no intermediate node exists to carry
its dependence. The ancestry requirement therefore rejects that joint-budget
configuration directly.

No ancestor implementation is certified by this mathematical note. The
companion JSON records the algebra check and scope. No solver, repository
mutation, lease action or running-file change was performed.
