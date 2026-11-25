# Hidden continuous symmetry: scoped obstruction

No witness or global nonexistence result is claimed. This exact symbolic calculation rules out a particular Borel-degeneration strategy.

Use tangent coordinates a,b,c,u,v,w,p,q,r in the symmetric matrix

    [a,u,v,w; u,b,p,q; v,p,c,r; w,q,r,-a-b-c-2(u+v+w+p+q+r)].

Let Q,C,F be the primitive homogeneous degree-two, three and four coefficients of permanent(J+zT)-24. The linear coefficient vanishes by construction. The Gram matrix G of Q is nonsingular, with determinant -54. Any infinitesimal linear transformation preserving the degree-two constraint is A=lambda I+G^{-1}K, with K skew-symmetric. To preserve the cubic modulo the quadratic, its skew part must satisfy

    grad(C) · (G^{-1}K x) = beta C + ell(x) Q.

The 36 skew coefficients, beta, and nine coefficients of ell give 46 columns in the 165-dimensional space of cubics. Multiplying all entries by 6 produces an integer matrix. It has full column rank: the stored 46-row minor has determinant

    8418752042204898664408548001917306368517570822144

and residue 205 modulo 1009. A separate fraction-free Bareiss calculation checked that exact integer determinant. Independent rook-sum expansions reproduce Q and C from the original matrix permanent.

Hence K=0, beta=0, ell=0. The identity component of the linear stabilizer of the graded constraint ideal <Q,C,F> is the scalar torus, which acts trivially on the Grassmannian of candidate planes. In particular, linear permanent symmetries fixing J cannot provide a useful connected group for Borel degeneration. This does not classify arbitrary nonlinear symmetries or prove absence of planes. The ideal-stabilizer assertion concerns the stated graded ideal, without making an unproved identification with its radical.

The obvious diagonal-congruence torus sends J to vv-transpose and does not fix J except for a finite subgroup. Its rank-one basepoint orbit in the nonzero permanent fiber is not projective; passing to its boundary can leave the affine fiber. Thus that torus does not immediately repair the fixed-basepoint problem.

The proposed transposition incidence argument also fails by dimension alone: the minus eigenspace has dimension three (diagonal00-11, edge02-12, edge03-13), so the fixed tangent space has dimension six in tangent dimension nine. A three-plane need not intersect it nontrivially.

Sources, exact coefficient matrix, selected minor and complete logs are frozen in /tmp/oec/pequalnp-pilot-75/gct231/concept/. `stabilizer_fast.py` generates the matrix, and `verify_stabilizer.py` checks its exact minor and independent rook coefficients. No Lean proof is claimed.
