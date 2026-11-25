# Independent review of the block-seed extension obstruction

Verdict: the exact symbolic argument is valid. The two-plane `T(x,y) = diag(xA,yA)`, where `A = [[sqrt(2)-1,1],[1,-sqrt(2)-1]]`, is a constant-permanent plane and cannot be extended to a three-dimensional linear solution space. This concerns that particular seed plane; it is not global nonexistence and is not Lean checked.

I reread and reran `/tmp/oec/pequalnp-pilot-75/gct231/fresh/block_seed/extend.py`, reproducing the four residual variables and their power reductions. I independently recomputed the full permanent of `J+T(x,y)+zB` using Ryser's subset formula; it agrees exactly with the script's permutation-sum polynomial.

The normalization `B01 = B23 = 0` is valid: subtract the corresponding multiples of the two seed generators from B. Each seed generator has its respective off-diagonal entry equal to one and the other equal to zero. This operation leaves the span of the seed and B unchanged.

All coefficients linear in z, together with that normalization, are solved by the displayed linear substitution. I checked that this substitution annihilates every linear coefficient. The residual equations have exactly the variables `b11, b13, b22, b33`. Exact Groebner reduction reproduces

    b11^5 = 0, b13^4 = 0, b22^5 = 0, b33^5 = 0

modulo the residual ideal. At any complex solution these coordinates therefore all vanish. Substitution of that origin makes every entry of normalized B zero, which I also checked. Thus every possible extension direction lies in the original seed span, so no independent third direction exists. No correction is needed.
