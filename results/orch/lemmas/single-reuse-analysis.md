# One-reuse core classification — informal analysis

This section is mathematical analysis, not a checked general classification.

A single core with U gates and U distinct input leaves has a connected fan-in-two multigraph with exactly one undirected cycle. Equivalently one wire is used twice and every other non-output wire is used once. Treat the repeated wire as a shared read-once subtree W.

## The cover-at-most-two shortcut is false

Take W = (x0 AND x1) OR (x2 AND x3), and core r = (W OR x4) AND (W OR x5). Its cone has six gates and six input leaves. It accepts the three disjoint matching edges 01, 23, 45, whose minimum cover size is three. Append the canonical matching output, leaving r dead, to satisfy the lift-fixedpoint condition. This concrete example is checked in DuplicateGate.lean, exit 0 and empty output; it is not a refutation of the posted inequality. The file also certifies that wire8 is used twice and every other non-output wire in the core cone once.

## Refined case analysis

- If the unique cycle merges strictly below the core output, the output AND has disjoint-variable operands. Its accepted-edge graph is a complete bipartite graph on the singleton supports of those operands; C4-freeness makes it a star.
- Otherwise the output AND combines read-once contexts F1(W,A), F2(W,B), with A, B and the inputs of W disjoint.
- If W rejects all singleton inputs, the reread pair forces both paths from W to the output operands to contain OR gates only. The root is (W OR H1(A)) AND (W OR H2(B)); its quadratic graph is the disjoint union of the quadratic graph of W and one cross star. The read-once W has a star-forest quadratic graph because the ambient graph has no C4. Thus the result is a star forest, possibly with large minimum cover.
- If W accepts a singleton, the output cannot have both W paths OR-only (that would accept the singleton). A reread pair also prevents both paths from having an AND, since those AND side branches use disjoint outside variables. Exactly one W path has one AND and the other has only ORs. The context has shape (((W OR H0) AND P) OR H1) AND (W OR H2). The sets of variables in H0,P,H1,H2 and W are disjoint.
- Let R be the singleton support of W, B that of P, C that of H1, and D that of H2. R and B are nonempty by the reread witness. The accepted graph has edges B-R, R-C, C-D. C4-freeness forces the non-star case to have R and C singleton, giving a double-star.

The conditional classification therefore predicts: gamma is a star forest or one connected double-star. Its edge-plus-cover-minus-vertex excess is at most one, which is exactly enough for the posted bound in the tight single-core case. Formalizing the unique-reused-wire normal form remains substantial.

A weaker Shannon argument from the counterexample agent reaches the easier conclusion that gamma is a forest: write F=f0 OR (W AND f1), with f0,f1 read-once in outside variables. The only new quadratic cross part is a star, and attaching it twice to an old star component would make a triangle or C4.
