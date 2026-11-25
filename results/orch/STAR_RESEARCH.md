# L-meta-2448 literature and exactness research

Read date: 2026-11-25. Web access was read-only; no shell requests to research hosts. No source proof changes. No counterexample to the posted statement or completed normalization argument found.

## What the primary sources establish

[Jukna, Disproving the Single Level Conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf), sections 3 and 8: the C4-free bound cited there is for single-level circuits; the paper separately poses superlinear lower bounds for explicit quadratic functions under unrestricted circuits. Its counterexamples use saturated extensions containing cliques, so they do not satisfy our girth assumptions. The paper's language is explicit: “the case of circuits is more complicated.” This is historical evidence of difficulty, not a current impossibility result. Current resolution of its Problem 8.2 is UNVERIFIED: searches found no modern primary source settling it.

[Katz, On the CNF-complexity of bipartite graphs containing no K2,2's](https://arxiv.org/pdf/1206.6068), definition on page 1 and Theorem 1.2: some C4-free bipartite graphs of large average degree admit graph-CNF representations using O(log d) clauses. Its clauses are unions of vertex stars and its conjunction is intersection of edge relations. This is graph representation, not a circuit proved equal to the edge function on all Boolean inputs.

[Jukna, Graphs and Circuits: Some Further Remarks](https://web.vu.lt/mif/s.jukna/ftp/dagstuhl2006.pdf), opening definition: representing a graph only fixes behavior on tested pairs. For bipartite representation, same-part pairs are not tested either. Therefore these upper bounds cannot be transplanted as exact graph-function circuit upper bounds.

The [Amano–Maruoka publisher abstract](https://doi.org/10.1007/s00453-006-0073-0) reports separations for conjunctive and single-level complexity. A primary full text was not accessible through the browser. Its detailed hypotheses and any application to girth at least five are UNVERIFIED; no numerical claim from that paper is used here.

## Direct deductions for this task

These deductions are from the task definitions, not claims copied from a paper, and are not Lean-checked here.

1. In a single-level circuit computing the exact edge function, every useful AND combines two ORs of variables. Their supports must be disjoint, since a common variable would make the output true on a singleton. Every cross pair must be a graph edge. In a C4-free graph, the resulting complete bipartite graph must be a star. Covering output edges with these stars yields a vertex cover with at most one center per AND. Conversely a vertex-cover star construction supplies such a circuit. This explains the vertex-cover AND count for single-level circuits; it does not prove the same lower bound for unrestricted circuits.

2. Exactness cannot be checked on pairs alone. For a matching with edges a_i b_i, adding a conjunction of three distinct a_i to its edge function preserves all singleton/pair answers but wrongly accepts an independent triple. Thus retaining only pair truth tables can lose the obstruction to exactness.

3. Pair-clean is weaker than globally below the graph function. A conjunction of an independent triple accepts no pair, so it vacuously satisfies pair-soundness, but it accepts that independent triple. Accordingly, the compiled pair-sound-to-star lemma is useful, while replacing its hypothesis by global soundness would make the missing normalization stronger.

4. Lowering one gate in a monotone circuit cannot create an output false positive. If the resulting monotone circuit still accepts every graph-edge pair, it computes the exact original edge function: each true input contains an edge and is accepted by monotonicity; every independent input remains false by the pointwise decrease. This gives a potential exchange criterion requiring only preservation of edge pairs, provided the transformation decreases the function pointwise.

5. In particular, a gate true on no graph-edge pair can be forced false without changing the function. After a valid deletion/reindexing, minimality excludes that gate. More generally, every gate of a minimum circuit must be pivotal on some graph-edge pair when forced false. This suggests defining a gate's critical edges, rather than treating every owned edge as equally necessary to the output. The actual reindexing and strict size decrease still need proof in the circuit model.

6. The known two-edge-matching circuit `(a OR c)(b OR d)(a OR d)(b OR c)` has dirty owning gates and neither input OR of its first AND is globally below the graph function: each accepts a singleton. It is larger than the elementary matching circuit, so it does not refute the least-circuit existential statement. The sibling finite-search agent reports optimal-size nonstar constraints for C5 and C6 as UNSAT; those reports are computational, not Lean verification by this reviewer.

## Assessment

No primary source read supplies the exact required size-preserving girth-at-least-five normalization. No known sparse-graph separation found here refutes the held statement. The main practical dangers are importing a single-level bound into an unrestricted circuit argument, transferring pair-test graph representations to exact functions, and replacing the existential optimal-circuit claim with an unsupported claim about every optimum.

The strongest independent local direction is the pointwise-decreasing exchange criterion above. Any attempt that raises a dirty gate to an operand or OR must additionally control newly accepted independent inputs; pair preservation alone is insufficient for such an increasing transformation.

Later checked progress: PivotalNecessary now proves the deletion/reindexing and minimum-circuit pivotality described in deduction5. These facts do not complete the global repair. The early research observations above are preserved with this update.
