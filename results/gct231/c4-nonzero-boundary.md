# Degenerate boundaries in the C4 product argument

This is a scoped mathematical argument using the reviewed rational C4 coordinates. It is not Lean checked. It concerns the quadratic and cubic necessary conditions only. The nondegenerate open cases still require their separate exact algebraic certificates.

Write

    q = 6e²+2f²+a²+b²−H²−X²−Y²−X(a+b)+Y(b−a),
    c = 2fab−2HXY + e(−4X²−4Y²+4X(a+b)+4Y(a−b)−a²−b²+4f²)−4e³.

For a putative three-plane L not contained in e=0, its intersection K with e=0 has dimension two. In the nonzero-product branch, unique factorization gives nonzero scalars α,β,γ with αβγ=1 and identifies (H,X,Y) with a scaled permutation of (f,a,b) on K. Let W3 be the three-dimensional graph of these three identifications. It contains K and satisfies c=0 at e=0.

The restriction of q to W3 has rank at most two, since it contains an isotropic two-plane. If its rank is zero, W3 itself is a quadratic/cubic-zero three-plane in e=0, excluded by the separately reviewed whole-hyperplane argument.

Suppose its rank is two. Its radical is a line spanned by r, and K contains r. Let W4(H,X) impose only the first two graph relations, and W4(H,Y) only the first and third. Adding one vector to a rank-two three-dimensional quadratic space gives a nondegenerate four-dimensional space precisely when its pairing with r is nonzero. Consequently, if both W4 spaces are degenerate, r is orthogonal to the ambient X and Y coordinate directions as well as W3. The ambient quadratic form on e=0 is nondegenerate. Its covector q(r,−) is therefore proportional to the first graph relation nH=H−αp, where p is the left factor matched to H.

Let G be the ambient six-dimensional Gram matrix, and N the matrix of the three graph-relation covectors. The first column of N G⁻¹ Nᵀ must vanish. When H matches a or b, this column contains α/3, which is nonzero. When H matches f, its only possibly nonzero entry is α²/2−1, forcing α²=2. Then r is proportional to the pure (f,H) direction with f=1,H=α. For any extension vector w, the coefficient of t in c(r+t w) is exactly 4e(w). Thus no such direction can lie in a cubic-zero L with e(w)=1.

It follows that the rank-two branch has a nondegenerate W4(H,X) or W4(H,Y). The exact symmetry

    (e,f,a,b,H,X,Y) ↦ (e,−f,a,−b,H,Y,X)

preserves both q and c and interchanges these choices. Thus the six open cases with nondegenerate W4(H,X) suffice.

For rank one, K equals the two-dimensional radical of q restricted to W3. If H matches f, the Gram matrix splits as (2−α²)f² plus a quadratic in a,b. When 2−α² is nonzero, the latter quadratic must be zero and K lies in f=0, contradicting the nonzero-product assumption. Otherwise K contains the same forbidden pure (f,H) direction.

The other four permutations reduce by the exact symmetry

    (e,f,a,b,H,X,Y) ↦ (−e,−f,b,a,H,X,−Y)

to two representative matrices. For (H,X,Y)=(αa,βf,γb), rank one and β≠0 force

    1−α² = 1−γ²+γ = −γ/2,
    β²(2γ−1)=4γ.

Hence γ is 2 or −1/2; the resulting value of (αβγ)² is respectively 64/3 or 3/16, contradicting αβγ=1. For (H,X,Y)=(αa,βb,γf), rank one similarly gives

    1−α² = 1−β²−β = β/2,
    γ²(2β+1)=4β.

Now β is 1/2 or −2, again yielding squared products 3/16 or 64/3. This excludes every rank-one boundary.

Exact scalar, Gram-column, and symmetry checks are in scratch `fresh/c4_boundary_checks.py/.log`. The script also independently checks the rank-one polynomial ideals, but the displayed finite alternatives make a Groebner result unnecessary for this boundary argument. Independent review is recorded separately when complete.
