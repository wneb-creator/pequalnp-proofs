# Common-kernel obstruction

This is a scoped mathematical argument supported by exact symbolic calculations, not a Lean proof and not a refutation of the unrestricted GCT-231 statement. The nonisotropic-kernel part has independent review in `common-kernel-review.md`; the isotropic completion independently passed in `isotropic-kernel-review.md` on 2026-11-25. The conclusion is that any solution three-plane would have trivial common kernel; this leaves planes with trivial common kernel entirely open.

Write j=(1,1,1,1). The linear and quadratic homogeneous permanent coefficients are 6jᵀTj and

    Q(T)=tr(T²)−2(Tj)ᵀ(Tj)

on the tangent hyperplane jᵀTj=0. No nonzero symmetric rank-one direction can belong to a solution plane: for T=vvᵀ, the kth coefficient is k!(4−k)! e_k(v)². Constancy makes every elementary symmetric polynomial of v vanish, hence v=0.

## A nonisotropic common kernel

Suppose Tk=0 for every T in a putative solution three-plane and kᵀk≠0. Let W=k-perpendicular, and let w be the orthogonal projection of j to W. Then wᵀw=jᵀw=s. Symmetric matrices annihilating k identify with symmetric endomorphisms of the nondegenerate three-space W.

If s≠0, choose an orthonormal coordinate with w=√s e1. The linear condition sets the (1,1) entry to zero. In the remaining five coordinates the quadratic form is

    2(1−s)(b²+c²)+d²+f²+2e².

For s≠1 this form is nondegenerate, so it cannot contain a totally isotropic three-space. For s=1 its two-dimensional radical must be contained in any isotropic three-space. In the original coordinates the radical is

    {wuᵀ+uwᵀ : jᵀu=wᵀu=0},  with jᵀw=wᵀw=1.

The exact saturation chart w0≠w3 writes w=(a,b,c,1−a−b−c), introduces h(w0−w3)=1, and computes all cubic and quartic conditions for this radical plane. Its Groebner basis is

    a²−a, h−2a+1, b, c.

Thus w is e0 or e3 in this chart. A nonconstant w has some unequal pair of coordinates, and relabeling covers it; a constant w cannot have both sum and squared norm one. Consequently the only radical planes are the standard zero-sum star planes. Their previously checked nonextension excludes a three-plane containing them.

If s=0 but w≠0, the tangent five-space has a quadratic form of rank four whose one-dimensional radical is wwᵀ. Every isotropic three-space contains this radical, contradicting the rank-one obstruction. The independent review checks this in coordinates w=(1,i,0). Finally w=0 means k is proportional to j, which is the separately checked row-sum-zero three-plane exclusion.

Exact source/log: scratch `fresh/common_kernel_radical.py/.log`; independent reproducer: `fresh/common_kernel_review.py/.log`.

## An isotropic common kernel with nonzero coordinate sum

Suppose kᵀk=0 and q=jᵀk≠0. Set l=j/q−2k/q². Then kᵀl=1, lᵀl=0, and j=q l+2k/q. Complete k,l to a Witt basis k,l,e,f with e,f orthonormal. Every symmetric matrix annihilating k has the tensor form

    a kkᵀ+b(keᵀ+ekᵀ)+c(kfᵀ+fkᵀ)
      +d eeᵀ+e0(efᵀ+feᵀ)+f0 ffᵀ.

The tangent equation is q²a=0, hence a=0. The restricted quadratic is

    d²+f0²+2e0²−2q²(b²+c²),

which is nondegenerate on five variables. Thus it has no isotropic three-space.

## An isotropic common kernel with zero coordinate sum

Now kᵀk=jᵀk=0. Choose the Witt basis so j=2e. The tangent equation above gives d=0, and the quadratic becomes

    f0²−6e0².

Its radical has dimension three and is exactly R={kuᵀ+ukᵀ:uᵀk=0}. An isotropic three-space intersects R in dimension at least two. Let U be the corresponding two-space of vectors u. It cannot contain k, because that would give the forbidden rank-one direction kkᵀ. The coordinate-sum functional is nonzero on U: otherwise U would equal the two-space k-perpendicular intersect j-perpendicular, which contains k.

The isotropic conic in projective j-perpendicular has the parameterization

    k(t)=H(0,1−t²,i(1+t²),2t)ᵀ,

where H is the unnormalized Hadamard matrix. The missing point is H(0,−1,i,0)ᵀ. For finite t, the vectors j,k,k′ form a basis of k-perpendicular. Therefore, after choosing the vector with coordinate sum four and subtracting a multiple of the zero-sum vector, U has a basis

    v=k′+λk, u=j+μk.

Both directions kvᵀ+vkᵀ and kuᵀ+ukᵀ would have constant permanent.

For the first direction, exact cubic and quartic coefficients have resultant R(t), a nonzero scalar times the degree-72 polynomial printed in `rowzero_nilpotent.log` and `isotropic_kernel_certificate.log`. A common zero of those two coefficient polynomials necessarily makes R(t)=0.

For the second direction, let A=e3(k), B=e4(k). Here

    A=−16it(t⁴−1), B=4(t⁸+14t⁴+1).

The exact cubic and quartic coefficients are

    48A(1+Aμ³),
    48B+72A²μ²+384ABμ³+384B²μ⁴.

If A=0, the following necessary polynomial already vanishes. Otherwise Aμ³=−1, and setting z=Bμ⁴ turns the quartic condition into (8z−3)(2z−1)=0. Thus in every case

    A(A⁴−8B³)(27A⁴−512B³)=0.

The certificate script computes the exact greatest common divisor of this polynomial with R and obtains one. It also emits and verifies an explicit rational Bezout identity in `isotropic-kernel-bezout.json`. Hence no finite t can satisfy the two required line conditions simultaneously.

At the missing conic point, the first direction has cubic coefficient −2048λ and quartic coefficient 6144λ⁴+3072. They cannot both vanish. This completes the proposed isotropic-kernel obstruction.

Exact final source/log: `fresh/isotropic_kernel_certificate.py/.log`, with the prefix of `rowzero_nilpotent.py` used to reproduce the resultant. The latter script's later FGLM conversion failed and is not part of the certificate. An earlier direct three-variable Groebner calculation of all mixed plane coefficients was stopped after the simpler resultant/Bezout argument replaced it. The separate infinity check is also in `isotropic_kernel_plane_infinity.log`. No solver timeout or failed conversion is used as evidence.
