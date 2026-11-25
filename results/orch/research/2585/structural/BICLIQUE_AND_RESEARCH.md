# Biclique cover versus AND count

Read/reasoned at 2026-11-25T01:06:24.685418+00:00. No proof or C4-free bipartite counterexample obtained.

For a C4-free bipartite graph every nonempty biclique is a star, so its minimum biclique edge-cover number equals its minimum vertex-cover number. Thus biclique-cover≤AND is exactly the proposed missing AND lower bound in this class, not an independently established shortcut.

The unrestricted all-graph claim is false: Jukna’s multiplicative gap construction gives full quadratic functions on saturated nonbipartite graphs with logarithmic AND complexity and linear biclique-cover complexity. This does not transfer to bipartite graphs.
Source actually read: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf , Theorem2.4 and its proof.

Two other apparent matches do not resolve our case:

- Katz defines graph CNF as intersections of clause graphs, so his C4-free low-CNF examples only specify pairwise graph representation. They do not prove full quadratic functions have small circuits on arbitrary subsets. Read definitions and Theorem1.2: https://arxiv.org/pdf/1206.6068 pp1–3.
- The semi-disjoint bilinear circuit method requires each variable to occur in at most one prime implicant of each output. A single output is then a matching, unlike general incidence graphs. Read Definition9.6.4 and Lemma9.6.2: https://cs.brown.edu/people/jsavage/book/pdfs/ModelsOfComputation_Chapter9.pdf pp420–421.

The dirty-gate obstruction persists even with exact full semantics: (a∨b)(c∨d)(a∨d) equals ac∨ad∨bd, a C4-free bipartite path. The first AND creates a rectangle containing the nonedge bc; a later AND filters it. Its final biclique cover still has2stars, equal to2AND, so it obstructs the naive per-birth-gate proof without refuting the proposed bound.

No applicable general theorem was located. Current2026 literature status is UNVERIFIED: targeted primary-source searches did not establish either a theorem or an impossibility result for full C4-free bipartite functions.

Counterexample agent queued an auxiliary4×4/3AND search with a diagonal fooling set while allowing other4cycles. A witness there would refute a stronger bipartite Boolean-rank bound but would not by itself refute our C4-free goal. No result yet.
