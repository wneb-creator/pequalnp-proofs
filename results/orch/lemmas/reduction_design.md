# Independent reduction review

The existing reduction R_meta_1768_1 splits exposed junk witnesses from residual nested witnesses. A semantic alternative via wmax/gammaE is not clearly smaller: one-gate contact bounds can sum to a quadratic total.

The proposed 3-core reduction is stronger as a research cut. It adapts the already checked R_meta_1735_5 generic peeling proof to the selected target-edge set.

## Hypothesis 1: essential-input bound

IsLeastAO G C implies G.support.ncard <= C.size + 1.

This is true. Every nonisolated vertex changes graphFun G empty at a suitable assignment and hence is an essential circuit input. A fan-in-two output cone with m internal gates contains at most m+1 distinct input wires. Unused gates only increase C.size. Minimality is not necessary, but retaining it is harmless.

## Hypothesis 2: bound the selected target's 3-core

For every subgraph H of the selected target-edge graph, if each vertex has degree zero or degree at least three, bound H.edgeSet.ncard by a universal constant times C.size+1.

This is genuinely restricted. Repeatedly deleting degree-one and degree-two vertices disposes of every 2-degenerate selected subgraph, including forests and cycles, at cost at most two edges per supported original input. H preserves the circuit and original graph hypotheses but has only a minimum-degree-three obstruction left.

## Assembly checks

Let T be the goal's target finset. Since T is a filter of Ustar and Ustar is G.edgeFinset minus starEdges, T is a subset of G.edgeFinset.

Define D = G.deleteEdges (G.edgeFinset minus T). Then D.edgeFinset = T. The peeling lemma returns H <= D and |E(D)| <= |E(H)| + 2*|support(D)|. D <= G gives support(D) subset support(G), so hypothesis1 and hypothesis2 yield (c+2)*(C.size+1).

No graph-girth transfer to H is needed because hypothesis2 retains girth of G. No decidable adjacency instance must escape the proof: classical supplies it for D and H when needed. Empty target graphs are handled uniformly.

Pending: inspect final Lean candidate, exact conclusion bytes, and checker-printed hypothesis lengths (at most 2000 characters each).

## Checked and finite-case evidence

The exact first hypothesis is already checked as PEqualNP.Outside.L_meta_2074 in lean/PEqualNP/Outside/L_meta_2074.lean (220 lines). This is stronger evidence than an unformalized input-cone argument, and means one child of the proposed reduction is already finished.

The counterexample agent reports exhaustive graph minima for n <= 4 satisfy the essential-input bound, with equality for a single edge, path of length two, matching of size two, and star on four vertices. All minimum circuits tested have empty junk and empty target. A nonempty girth-five 3-core needs at least ten vertices, with the Petersen graph as the first possible size. The agent is separately checking generic peeling on all graphs through six vertices.
