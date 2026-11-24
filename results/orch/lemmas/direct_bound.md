# Direct-bound strategy and target-core reduction

The target is the type-A part of Ustar: an edge with one endpoint OR-reaching a top operand and an active dirty AND gate OR-reaching the opposite operand.

The checked file R_meta_1768_1 already splits this into exposed dirty-gate witnesses (both dirty operands directly OR-reach endpoints) and nested residual witnesses. Repeating that split would add little. The main obstruction to tracing all target edges to exposed witnesses is that OR closure stops at each AND; moving to a deeper dirty gate loses the required OR path from the original top.

Checked cases discovered:
- L_meta_1876: no dirty AND gates implies Ustar is empty.
- L_meta_1878: one dirty AND gate gives |Ustar| <= 12*(size+1). Its proof covers Ustar by three bicliques, then bounds the input-occurrence set by 2*size.
- L_meta_1766: exact structural split into type-A witnesses and two distinct dirty-gate witnesses.
- L_meta_2074: the essential-input support bound G.support.ncard <= C.size+1; independently located by reduction_design.

The direct multigate route did not close: each dirty gate individually admits a size-dependent charge, but summing that over dirty gates creates a quadratic bound. A missing disjointness/amortization argument is the substantial unresolved step, not a routine Lean lemma.

A distinct concrete reduction is in reduction_core.lean. It assumes the existing essential-support estimate and a linear estimate only for subgraphs of the exact selected-edge graph whose nonisolated vertices all have degree at least three. The proof removes degree-one and degree-two vertices by strong induction on support cardinality, charging at most two edges per removed essential input. The selected-edge graph is represented as G with G.edgeFinset minus the target edge set deleted. It is a subgraph of G and its edge finset is exactly the target set. The final constant is k+2.

Static API review corrected SimpleGraph.edgeFinset_mono: it is already the implication from graph inclusion to edge-finset inclusion, so no .mpr is used. Compilation awaits root-managed cache setup. No direct-bound proof claimed.

## Further direct analysis

For each target witness anchor u and dirty gate g, top cleanliness implies u belongs to wmax(g), so g is false on the singleton u. Under the restriction x_u=true, target neighbors v are singleton-true inputs of g. They propagate through OR gates and through AND gates whose other child is singleton-true on u. C4-freeness limits shared neighbor sets for two distinct anchors, but the same original gate can have different restricted behavior at different anchors. The unresolved step is bounding these anchor-dependent changes across nested AND gates. No proof that the selected-edge 3-core is empty was found.

The finite-degree peeling does not claim such emptiness: Petersen is a nonempty girth-five 3-core, so graph girth alone cannot remove the core. Any full proof must use additional circuit leastness/top-form information. The reduction keeps that information explicitly in its core premise.
