# Independent source review: adapted pencil square

PASS for frozen `AdaptedPencilSquare.lean`, SHA256 `c77f742ab8c2fb96fb499f1445831d51662a55a06f95bcf17ffed47081704d78` (95 lines). The previously reviewed 53-line polynomial-square foundation is preserved exactly. The new block decomposition uses symmetry only to identify the lower-left block with the transpose of the upper-right block. Congruence preserves symmetry. The final theorem forms the polynomial pencil N-XM, transports its two zero blocks through the same constant P, and applies the checked constant-congruence square theorem.

Both original forms are explicitly symmetric, det(P) is explicitly nonzero, and both adapted upper-left blocks are explicitly zero. The result is the determinant polynomial square for that adapted pencil. Constructing P from a two-dimensional common isotropic subspace remains a separate obligation; no existence assertion about the posted gap is made.

Source scan found no sorry, new axiom, native_decide, prohibited root text, or string literal. Narrow scratch imports still need reconciliation with allowed gap imports in final integration. The author reports a successful compile; this independent review did not rerun it.
