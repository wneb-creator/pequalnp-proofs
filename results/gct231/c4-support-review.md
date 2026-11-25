# Independent four-cycle-support chart review

Verdict: the rational seven-dimensional frame and complete eight-chart parameterization are correct. They cover every candidate solution three-plane with entries T02=T13=0. This is a sparsity restriction, distinct from stability under a four-cycle. No chart solution or nonexistence verdict is established by this review.

Exact independent source and full output are `/tmp/oec/pequalnp-pilot-75/gct231/fresh/c4_support_review.py` and `c4_support_review.log`. The log records source/export hashes and UTC timestamps. No Groebner basis calculation was rerun.

Ryser's subset formula independently reproduces all three homogeneous coefficients in `c4-support-homogeneous.json`. The displayed seven-coordinate matrix is symmetric, has the two required zero entries, and has total entry sum zero. Its quadratic Gram determinant is exactly -1728, so this is a nondegenerate quadratic on the full seven-dimensional tangent space for the restriction.

In the Hadamard coordinates used in the source,

    4T02 = -d1+d2-d3+2b2-2o2,
    4T13 = -d1+d2-d3-2b2+2o2.

Thus the support conditions are equivalent to `d2=d1+d3` and `b2=o2`. Writing `d1=(u+v)/2`, `d2=u`, `d3=(u-v)/2` gives quadratic weights

    (3/2, 1/2, 2, -4, 2, -6, -6)

in coordinate order (u,v,o1,o2,o3,b1,b3). The map P to the seven exported coordinates has determinant -1/2 and exactly transforms the quadratic as claimed.

All explicit E/F/Z vectors are correct. Their Gram matrix has three hyperbolic pairs with pairing one and a perpendicular residual vector of norm 12. The resulting frame in exported coordinates has determinant 1/12. These identities were checked independently, including all signs and factors 1/12 and 1/8 in F.

For any of the eight pair-swapping choices, normalize the three pivot coordinates to the identity. A plane then has columns `E + FB + Zr`, where r is a one-by-three row. Its Gram equation is

    B+Bᵀ+12rᵀr=0,

equivalently `B=K-6rᵀr` for a skew-symmetric K. This proves the graph formula in both directions and its six-parameter count. The independent reviewer checks all eight chart formulas identically. Their normalized pivot block also ensures that each represents an actual three-plane.

Coverage is complete. For any j of the three hyperbolic pair groups, the kernel of their coordinate restrictions to an isotropic three-plane lies in a nondegenerate complement of dimension 7-2j. Its isotropic dimension is at most 3-j, so the restrictions have rank at least j. The independent-transversal induction then selects three independent coordinates, one from each pair. Hence some one of the eight pivot choices is invertible. The extra residual line does not create an omitted chart.

Finally, the worker correctly substitutes these graph coordinates into the cubic and quartic homogeneous coefficients and clears nonzero coefficient denominators. Four selected exact assignments in chart zero were checked with an independent Ryser permanent; all 25 exported equations agree with the corresponding coefficients up to fixed nonzero denominator-clearing factors. These sample checks support the generator review and do not constitute a solution of the six-variable systems. The chart-coverage argument has not been formalized in Lean.
