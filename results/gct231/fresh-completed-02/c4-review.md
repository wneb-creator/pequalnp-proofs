# Independent four-cycle review

Verdict: the argument correctly excludes a complex solution three-plane stable under a four-cycle of the vertices. It is an exact symbolic obstruction, not a Lean-checked proof and not general nonexistence.

The independent review finished at **2026-11-25 10:21:13 UTC**. Source and complete output are `/tmp/oec/pequalnp-pilot-75/gct231/fresh/c4_review.py` and `c4_review.log`. The log records hashes of the two reviewed generators. Every permanent calculation in the review uses Ryser's subset formula, independently of their permutation sums.

The displayed matrices satisfy the claimed character equations entrywise. The character multiplicities in the full symmetric space are 3,3,2,2 for eigenvalues 1,-1,i,-i. The tangent condition reduces only the fixed space, giving dimensions 2,3,2,2.

In the fixed tangent space, the quadratic and cubic coefficients are

    8(3u²+2uv+v²),  -16u(u+v)².

Their simultaneous vanishing forces u=v=0: the cubic gives u=0 or u+v=0, and the quadratic then forces zero in either case. Hence a solution plane has no fixed component.

In the -1 space, the quadratic is `-4(a²+4ac-2b²+c²)`, with Gram determinant -384. Its isotropic subspaces have dimension at most one.

In each of the i and -i spaces, only the quartic remains. Its factorization is respectively

    -i v²(4u²-i v²),  i v²(4u²+i v²).

Each zero set is exactly the union of the three lines listed by the generator: v=0 and the two normalized solutions with v=1. Thus a solution subspace in either character space has dimension at most one.

The independent review checks all nine choices of one line from each of these two character spaces. Every corresponding two-plane fails the permanent identity. For the pair with both v=0, the coefficient of y²z² is 16. If both normalized v-values are one, that coefficient is 1. In the remaining four pairs, a nonzero yz coefficient is recorded explicitly in the log over the exact algebraic field Q(i,sqrt(2)). There is no missed projective line or boundary case.

Finally, a four-cycle acts semisimply over the complex numbers, so any stable subspace splits into its character intersections. A solution three-plane would have to contain one nonzero line in each of the -1, i, and -i spaces. Its i and -i components would then give one of the forbidden nine two-planes. This proves the stated scope without requiring an extension calculation involving the -1 component. No correction is needed.
