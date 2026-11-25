# Forest route: mathematical argument and checked compiler pieces

This is a partial research record, not a Lean proof of the forest theorem or L-meta-2585.

For a nonempty forest G, the intended sharp cost is |E(G)| + tau(G) - 1. Root and sibling simplified the initial total-cost recurrence into separate operation counts:

* OR count at least |E(G)| - 1. Delete a leaf y by setting y=0. If another edge remains, the restricted function is nonzero. Since y was essential, an input-to-output path exists. An all-AND path would force the restricted output to zero; hence a first OR lies after an AND-only path from y. Its input becomes false and constant propagation eliminates that OR. Induct on edges.
* AND count at least tau(G). For a pendant edge xy with leaf y, first set y=1 and then x=0. The remaining graph is H=G-{x,y}, and tau(G)=1+tau(H). Because the original function rejects the singleton y, no y-to-output path can be all OR; a first AND after an OR-only prefix receives true and is eliminated during y=1 propagation. Setting x=0 cannot increase AND count. Induct on the forest. Empty residual cases need the obvious nonempty-edge base.

The operation-path argument presumes dead gates have been removed, or a path from an essential input is chosen. Constants are propagated completely; final nonconstant restricted functions are represented without constants. Exact binary AND/OR shape is preserved.

Checked sources:

* ForestElim.lean: compiler prefix and semantic invariant adapted from L-meta-2502 (which credits L-meta-1543), plus annihilator status propagation and a two-distinct-gate deletion budget.
* ForestElimCounts.lean: additionally adapts L-meta-2752 operation-count monotonicity and proves elim_opCount_drop, which saves one selected operation whenever a selected gate receives a constant input.
* ForestElimAO.lean: additionally proves AOClean preservation through the compiler under its validity/semantic invariant and converts AOClean to TopForm.IsAO2. Full AO2 input-restriction packaging and path-to-constant lemmas are not yet assembled.

The initially found total-cost recurrence is also consistent: sibling-leaf removal preserves tau and saves one gate; otherwise a deepest internal vertex has one leaf child and degree at most two. A live AND reading the leaf is annihilated by leaf=0 together with a later reader, saving two. If leaf readers are OR, leaf=1 saves two, then its neighbor=0 saves another when the residual graph is nonempty. This route needs more cases than the split-count induction.

## Explicit cyclic obstruction to this induction

A C4-free cyclic core need not have any leaf (C6 already has none). For a degree-d vertex y, setting y=0 deletes d edges, but the first-OR argument guarantees only one OR deletion, creating a deficit of d-1. Setting y=1 produces unit terms at every neighbor; eliminating all those neighbors can change the cover number by as much as d, but the first-AND argument guarantees only one AND deletion. Neither compiler accounting nor C4-freeness itself supplies the missing d-1 gates. Thus this route gives a plausible complete forest proof while identifying a concrete failure of the recurrence on cyclic cores, not a solution of the full posted statement.
