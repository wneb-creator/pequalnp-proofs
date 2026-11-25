# GCT-231 fresh algebraic investigation

Exact target: a three-dimensional complex linear subspace of symmetric 4-by-4 perturbations t with permanent(J+t)=24 identically. No proof or refutation of the full statement has been obtained. All computations below are exact symbolic mathematical evidence unless explicitly marked numerical; none has yet been translated into Lean.

## Standard star plane cannot extend

Let T(x,y) have first row/column (0,x,y,-x-y) and all other entries zero. This is a two-dimensional constant-permanent plane. For a symmetric candidate B, requiring the coefficient of z in permanent(J+T(x,y)+zB)-24 to vanish identically forces the lower-right 3-by-3 block of B to be constant c and B00=-2S-9c, where S=B01+B02+B03. The remaining coefficients include

- z²: 2(S²-6Sc-63c²),
- z³: 4c(S²-6Sc-39c²).

Subtracting c times the first reduced equation from the second reduced equation gives 24c³=0. Over the complex numbers c=0, then S²=0 forces S=0. Hence B already lies in the original star plane. Script: scratch gct231/fresh/star_extend.py.

## Rank-two fixed-vector ansatz cannot work

For t=u vᵀ+v uᵀ with sum u=0, u·u=0, v·u=0, the linear and quadratic permanent coefficients vanish. However the three-dimensional parameter space u-perpendicular contains v=u, hence contains the nonzero symmetric rank-one direction 2uuᵀ. No nonzero symmetric rank-one direction is constant-permanent: permanent(J+a uuᵀ)=sum_{k=0}^4 k!(4-k)! e_k(u)^2 a^k. Constancy forces all e_k(u)=0, so all coordinates of u are zero. Thus this full three-dimensional ansatz is impossible.

## Sparse block obstructions

For a fixed 2+2 symmetric block-diagonal perturbation, let sA,sB be the sums of the entries of the two blocks, and pA,pB their permanents. The homogeneous equations force sB=-sA, pA+pB=sA², sA(pB-pA)=0 and pApB=0. In the polynomial ring on the proposed linear space, this implies sA=sB=pA=pB=0. Each symmetric 2-by-2 block with these conditions contributes at most one linear dimension, so the total dimension is at most two.

The triangle-coordinate-support case is a 3+1 block decomposition t=diag(A,d), with A symmetric 3-by-3. Write s for its entry sum, r for its degree-two rook sum and p for its permanent. The four homogeneous equations force d=-s, r=s², p=s³ and dp=0, hence s=d=r=p=0. The second-rook quadratic on symmetric 3-by-3 matrices with entry sum zero is nondegenerate on a five-dimensional space, so its totally isotropic subspaces have dimension at most two. This rules out three-dimensional families supported on one offdiagonal triangle, even with arbitrary diagonal linear forms.

## Twenty-four zero-diagonal planes and extension checks

Write the six offdiagonal entries as a=t01,b=t02,c=t03,d=t12,e=t13,f=t23. Let opposite-edge sums p=a+f,q=b+e,r=c+d and differences x=a-f,y=b-e,z=c-d. With p+q+r=0, the homogeneous conditions reduce to

    x²+y²+z²=p²+q²+r²,
    xyz=pqr.

The quartic coefficient is the square of the quadratic expression divided by sixteen and gives no further condition. Any signed permutation (x,y,z) of (p,q,r), with product of the signs equal to one, therefore defines a constant-permanent two-dimensional plane. The script planes_extend.py checks all twenty-four distinct such planes. In every case, the linear variation equations for a third direction followed by the remaining coefficients force that direction back into the original plane. Some cases reduce to the star obstruction above; the three-cycle permutation cases reduce directly to a residual coefficient -16c². The full exact output is planes_extend.log. This is not a classification of all zero-diagonal two-planes.

A zero-diagonal three-plane is impossible already from the quadratic coefficient: after the total-entry-sum equation, the offdiagonal tangent space is five-dimensional with nondegenerate quadratic form, so maximal isotropic dimension is two.

## Full triangle chart

The offdiagonal projection of any putative three-plane is injective: a nonzero diagonal direction cannot have constant permanent, since its four elementary symmetric polynomials would all vanish. Thus three offdiagonal entries can be chosen as coordinates. Up to vertex permutations the pivot patterns have three graph types: star, triangle, and path. Finite_cases coordinates the common exact generator; this agent owns triangle.

The full triangle chart uses t01=x,t02=y,t12=z, permits arbitrary linear forms for the other three offdiagonal entries and the first three diagonal entries, and eliminates t33 by the degree-one equation. There are eighteen complex unknowns and thirty-one homogeneous coefficient equations. A bounded exact Groebner computation and an independent numerical complex least-squares candidate search are running. Numerical residuals alone will not be treated as a proof of nonexistence or as an exact construction.

## Completed full triangle searches

The exact full triangle Groebner run reached its native 300-second limit with `UNKNOWN_TIME_LIMIT`; no basis or nonexistence verdict was returned. The simpler triangle-support Groebner run also timed out at 180 seconds, although the independent 3+1 block/Hessian argument above handles that restricted case.

Numerical candidate generation completed 100 initial complex random starts, 1,000 additional starts at scales 0.01, 0.1, 1, 3, 10 and 30, and 200 staged runs which first solved the quadratic/cubic conditions and then increased the quartic weight through 0.01, 0.1 and 1. No root was found. The best maximum coefficient residual in the 1,000-start run was approximately 0.103411568, at coefficient norm approximately 4.4158. These are failed searches, not nonexistence evidence. Scripts and full logs are numeric_triangle*.py/log in scratch gct231/fresh.

## Three-cycle-stable planes are excluded

This is a scoped exact symbolic argument, not a general classification and not Lean checked.

Let a 3-cycle permute vertices 1,2,3 and fix vertex 0. Its invariant tangent matrices have diagonal (a,c,c,c), entries b from vertex 0 to the other vertices, and entries d between the last three vertices. The linear condition gives a=-6b-3c-6d. The remaining coefficients are

    -6*(-3b²+2bc+4bd+2c²+10cd+9d²),
    -4*(-3b²c-6b²d+3bc²+6bcd+9bd²+2c³+9c²d+15cd²+13d³),
    -3*(-b²c²-2b²cd-3b²d²+2bc³+6bcd²+4bd³+c⁴+2c³d+3c²d²+8cd³+4d⁴).

Their normalized chart b=1 has exact Groebner basis [1]. On b=0,d=1 the basis is also [1], and b=d=0 forces c=0 from the quadratic coefficient. Thus there is no nonzero invariant constant-permanent direction. Exact generator/results: c3_invariant.py/log.

For a primitive cube root w, one nontrivial character space consists of matrices

    [0, u, u*w, u*w²;
     u, v, q, q*w²;
     u*w, q, v*w, q*w;
     u*w², q*w², q*w, v*w²].

Here the linear, quadratic and quartic coefficients vanish automatically, while the cubic is

    2q³-3q²v(w+1)+6qu²w-6quvw+3u²v+6uv²+v³.

This projective cubic is smooth: on q=1 its three derivative equations together with w²+w+1 have exact Groebner basis [1]; on q=0 the derivatives directly force u=v=0. Hence it has no linear factor over the complex numbers and its zero set contains no two-dimensional vector subspace. The conjugate character space has the same property.

Any three-dimensional plane stable under this 3-cycle splits into its three character spaces. It cannot contain a nonzero invariant vector, and distributing three dimensions among the other two character spaces forces a two-dimensional subspace in one of them, which the smooth cubic excludes. Thus no C3-stable three-plane solves the target. This does not exclude arbitrary planes lacking the symmetry. The larger seven-variable C3-stable chart computation was stopped once the invariant-line obstruction made it unnecessary.

## Independent review and additional completed checks

The C3 obstruction was independently checked by agent `/root/fresh_main_proof/c3_review`, with a second permanent implementation using Ryser's formula. Its review is `c3-review.md`, completed 2026-11-25 09:55:56 UTC. This is the only child agent spawned by this branch across both assigned gaps; the same child was subsequently reused for C2-stable planes.

The separate verification of all twenty-four zero-diagonal plane extension calculations completed with twenty-four PASS records. For every plane it computes a Groebner basis of the remaining coefficient ideal and verifies that a power of every linear form annihilating the original plane belongs to that ideal. Thus the radical condition forcing every extension direction into the original plane is checked directly. An initial run stopped at a rational-coefficient coercion error; explicitly using the rational polynomial domain fixed this, and the full rerun completed. Script/log: `fresh/planes_extend_verify.py/.log` under scratch.

A chart-independent numerical search used an orthonormal basis of the full nine-dimensional tangent space and represented a candidate plane by a complex 9-by-3 matrix. Nine real Hermitian Gram conditions fixed its columns to an orthonormal frame and prevented rank collapse. All thirty-one homogeneous permanent coefficients were included, with an analytic Jacobian checked against finite differences (relative error about 5e-10). One hundred random starts completed in about 146 seconds without a root; the best residual remained around 0.0013. These numerical failures do not prove nonexistence. Script/log: `fresh/numeric_grassmann.py/.log`.

## A nonzero-diagonal two-block plane is also nonextendable

Let r=√2 and A be the symmetric 2-by-2 matrix with diagonal (r−1,−r−1) and offdiagonal 1. Its entry sum and permanent are both zero. Therefore T(x,y)=diag(xA,yA) is a two-dimensional family satisfying permanent(J+T)=24.

For an arbitrary symmetric third direction B, subtracting a linear combination of the two seed directions allows B01=B23=0. The coefficients linear in z of permanent(J+T(x,y)+zB)−24 then express all entries of B through B11, B13, B22, B33. The exact remaining coefficient ideal over Q(√2) has a Groebner basis containing B33^5. After B33=0, its equations give B22^3=0, then B13^3=0, then B11²=0. Thus every such B is zero modulo the seed plane.

The computation also directly checks ideal membership of B11^5, B13^4, B22^5 and B33^5. This proves only that this particular two-plane has no three-dimensional extension. It does not classify all planes with nonzero diagonals. Exact script/log: `fresh/block_seed/extend.py/.log` under scratch; completed 2026-11-25 10:01 UTC. This is symbolic mathematics, not a Lean-checked theorem.

## Completed archive and general Witt reduction

The completed C2, C3 and nonzero-diagonal block-seed source/logs/reviews were copied into `results/gct231/fresh-completed/` and frozen at 2026-11-25 10:09:38 UTC. Its SHA256SUMS hash is `fb1af66897a01f010441fd273e9cf0b21ed144957611d72e538bc009bbe16699`; every listed checksum passed. A standalone independent Ryser reproducer is included. These archived files are read-only and will not be changed. The C2 result excludes transposition-stable planes; it does not by itself exclude planes stable only under a double transposition. The latter partial investigation is separately scoped in `double-transposition.md`.

A rational Witt frame for the full nine-dimensional tangent quadratic now gives an exact twelve-variable open chart. Its full ten cubic and fifteen quartic equations have been exported, and a complete family of thirty-two charts over Q(i) has a coverage argument independently assessed by finite_cases. The formula, scope, file paths and coverage argument are recorded in `witt.md`. No unit-ideal result or candidate solution is claimed for the general chart.
