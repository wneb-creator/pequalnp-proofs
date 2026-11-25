# Independent source review: common isotropic plane

PASS for frozen `CommonIsotropicPlane.lean`, SHA256 `ddd00bd47c8437801018a3ecb47e1929f2527ad63efdfd88ee328ed611838756` (200 lines). The previously reviewed 145-line algebraic foundation is preserved exactly apart from imports. The basis construction chooses a complementary subspace, proves its dimension is two from the four-dimensional ambient space, combines the two finite bases, and maps through the complement isomorphism. Its first two basis vectors lie in W. The column matrix is nonsingular because those columns form a basis, hence its determinant is nonzero.

The final theorem applies this adapted matrix to the already reviewed quadratic-columns theorem. It correctly concludes that the determinant pencil of two symmetric complex 4-by-4 forms sharing a two-dimensional totally isotropic subspace is a polynomial square. No additional geometric normalization is assumed or claimed, and this does not itself prove the posted gap.

No prohibited constructs were found. The author reports successful compilation; no duplicate compile was run. Narrow scratch imports still need reconciliation with allowed gap imports at integration.
