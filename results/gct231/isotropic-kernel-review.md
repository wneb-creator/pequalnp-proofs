# Independent isotropic-common-kernel review

Verdict: the proposed completion is valid. It excludes a solution three-plane with any nonzero isotropic common kernel vector. Combined with the prior nonisotropic-common-kernel obstruction, this excludes all solution three-planes having a nonzero common kernel. It does not exclude arbitrary solution three-planes, and the geometric argument and certificates have not been formalized in Lean.

The independent exact check completed at **2026-11-25 10:28:53 UTC**. Source and full log are `/tmp/oec/pequalnp-pilot-75/gct231/fresh/isotropic_kernel_review.py` and `isotropic_kernel_review.log`. Source and certificate hashes are recorded in the log. The failed, unused FGLM calculation in `rowzero_nilpotent.py` was not executed or used.

## Quadratic reductions

Take a Witt basis k,l,e,f, with k and l isotropic, `kᵀl=1`, and e,f orthonormal and perpendicular to them. Every symmetric matrix killing k is uniquely

    T = a kkᵀ + b(keᵀ+ekᵀ) + c(kfᵀ+fkᵀ)
        + d eeᵀ + e_var(efᵀ+feᵀ) + f_var ffᵀ.

These are tensor formulas in the original bilinear space. The independent checker uses the explicit Witt Gram matrix to compute the linear and quadratic permanent conditions.

If `q=Σk` is nonzero, one can choose `1=q l+(2/q)k`, since the all-ones vector has norm four. The tangent equation is `q²a=0`. On a=0 the quadratic is

    d²+f_var²+2e_var²-2q²(b²+c²),

whose Gram determinant is `8q⁴`. It is nondegenerate on five variables, so it has no isotropic three-plane.

If `Σk=0`, choose the all-ones vector to be 2e. The tangent condition is d=0, and the quadratic becomes `f_var²-6e_var²`. Its radical is exactly the three-dimensional space

    R = { kuᵀ+ukᵀ : u ∈ k⊥ }.

The nondegenerate quotient has dimension two, so an isotropic three-plane intersects R in dimension at least two. The map from u to its displayed symmetric tensor is injective for nonzero k. Its inverse image therefore contains a two-plane U. It cannot contain k, because that would give the forbidden nonzero rank-one direction `2kkᵀ`. The sum functional on U is nonzero: otherwise U would equal the two-dimensional space `k⊥ ∩ 1⊥`, which contains k.

## Coverage of the necessary two directions

Using the unnormalized Hadamard matrix H, every projective nonzero k with `Σk=kᵀk=0` is represented either by

    k(t)=H(0,1-t²,i(1+t²),2t)

for a finite complex t, or by the single point `k∞=H(0,-1,i,0)`. This is the complete smooth-conic parameterization: in conic coordinates the finite chart is `z1-i z2 ≠ 0`, with `t=z3/(z1-i z2)`, and its complement is exactly the stated infinity point.

For finite t, `Σk′=kᵀk′=0` and `k′ᵀk′=16`. Thus 1,k,k′ are independent and span k⊥. The one-dimensional kernel of sum on U avoids k, so its generator can be normalized to `v=k′+λk`. Choose the other generator with sum four, then subtract a multiple of v; it becomes `u=1+μk`. This covers every U under consideration. The omitted direction v=k would already be the forbidden rank-one case.

It is enough to require the two individual directions `kvᵀ+vkᵀ` and `kuᵀ+ukᵀ` to be constant-permanent. No assumption about their mixed coefficients is needed for the contradiction.

## Independent elimination and certificate replay

Ryser's subset formula independently reproduces the first direction's cubic and quartic coefficients. Their resultant in λ has primitive polynomial R(t) of degree 72, exactly matching the exported R. Any common finite λ-root forces this resultant to vanish, including specializations where a leading coefficient drops.

Let A=e3(k) and B=e4(k). The independent computation verifies

    A=-16it(t⁴-1),  B=4(t⁸+14t⁴+1),
    C3=48A(1+Aμ³),
    C4=48B+72A²μ²+384ABμ³+384B²μ⁴.

The resultant of the last two expressions in μ is exactly

    73383542784 A⁴(A⁴-8B³)(27A⁴-512B³).

Therefore the proposed weaker product condition is necessary, including A=0. Substitution into its primitive rational form yields the exported degree-53 polynomial Y(t). The reviewer reconstructs both R and Y independently, reads the rational coefficients in `isotropic-kernel-bezout.json`, and verifies the exact polynomial identity

    bezout_R(t) R(t) + bezout_Y(t) Y(t) = 1.

Hence there is no finite t satisfying both necessary conditions.

At infinity, use the derivative of the reciprocal conic parameter, `H(0,0,0,2)`, in place of k′. Independent Ryser expansion gives cubic `-2048λ` and quartic `6144λ⁴+3072`, which cannot vanish simultaneously. This closes the remaining projective point. No missing boundary case or correction was found.
