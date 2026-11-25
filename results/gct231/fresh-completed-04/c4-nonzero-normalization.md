# Necessary equations in the nonzero-product C4 branch

This note explains the geometric premises of the exact systems exported by `fresh/c4_nonzero_square_system.py`. It is scoped mathematical reasoning, not a Lean-checked theorem. The rational coordinate formulas and the case2/3 reductions have independent exact reviews.

Let q and c be the corrected C4 quadratic and cubic, and let L be a three-dimensional subspace on which they vanish. Suppose e is nonzero on L and K=L∩{e=0} has nonzero product fab=HXY. Unique factorization on the two-dimensional K identifies (H,X,Y) with (αp,βq,γr), where (p,q,r) is a permutation of (f,a,b), the three scales are nonzero, and αβγ=1.

Let W4 be the subspace of e=0 cut out by H=αp and X=βq. The remaining relation is the linear form ℓ=Y−γr. In the open case, the restriction G_W of the ambient quadratic Gram matrix G to W4 is nondegenerate. K is a two-dimensional totally isotropic subspace of the four-dimensional W4. Therefore its orthogonal complement inside W4 equals K.

Choose w∈L with e(w)=1. The e=0 part of w decomposes uniquely as w_W+w_perp for W4 and its ambient orthogonal complement. Since w is orthogonal to K, w_W belongs to K. Subtracting w_W from w preserves membership in L and e(w)=1. Thus one can take

    w = e_axis + G⁻¹(u n1+v n2),

where n1,n2 are the ambient covectors H−αp and X−βq. This is the exact formula used in the generator; no division depending on the graph scales occurs here.

The form ℓ vanishes on K. Its quadratic dual G_W⁻¹ℓ therefore belongs to the orthogonal complement of K inside W4, hence to K itself. The polynomial vector

    nv = adj(G_W) ℓ

also belongs to K. Consequently the following are necessary:

* `normal_q = ℓᵀ adj(G_W) ℓ = 0`.
* `q(w)=0` and `c(w)=0`.
* `normal_R = nvᵀ G_R nv = 0`, where R(k) is the coefficient of t in c(k+t w) and G_R is its symmetric Gram matrix.
* `normal_L = ℒ(nv)=0`, where ℒ(k) is the coefficient of t² in c(k+t w).

The implementation computes

    R(k) = Σ_i (∂_i c)(k) w_i,
    ℒ(k) = (1/2) Σ_ij (∂_i∂_j c)(k) w_i w_j.

An independent review recomputes these by direct substitution into c(k+t w), so `normal_L` is the mixed coefficient with two copies of w and one copy of k.

There is one further necessary condition. R vanishes on all of K, just as q does. In a basis of W4 whose first two vectors span K, both Gram matrices have zero upper-left2×2 block. Hence det(G_R−λG_W) is a square polynomial up to a nonzero constant. For its quartic coefficients d4,d3,d2,d1,d0, with d4≠0, this implies

    8 d1 d4² − 4 d3 d2 d4 + d3³ = 0.

The smaller exported systems initially omit this condition. Their isolated rational candidate lifts fail it: the determinant is λ³(13λ−4)/4 and the displayed coefficient expression equals −1. Both square-root choices in lifting the reduced case2/3 variables have been checked.

Exact sources: scratch `fresh/c4_nonzero_square_system.py`, `fresh/c4_nonzero_reduce.py`, `fresh/c4_nonzero_reduced_review.py`, and `fresh/c4_reduced_root_obstruction.py`, with matching complete logs and JSON exports. The separate boundary note explains why the nondegeneracy hypothesis can be arranged or the remaining boundary excluded.
