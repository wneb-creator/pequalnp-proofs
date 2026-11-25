# Independent common-kernel review

Verdict: the proposed reduction and the new radical-plane classification are correct. Together with the previously established standard-star nonextension and row-sum-zero obstructions, they exclude a solution three-plane having any nonzero common kernel vector k with `kᵀk ≠ 0`. This does not cover isotropic common kernel vectors or planes without a common kernel, and it is not a Lean-checked result.

All dot products here are complex bilinear, without conjugation. The independent exact check finished at **2026-11-25 10:20:08 UTC**. Source and full successful output are `fresh/common_kernel_review.py` and `fresh/common_kernel_review.log` under `/tmp/oec/pequalnp-pilot-75/gct231/`. The log records the reviewed generator's SHA256. A first review-script attempt failed only because it compared an expanded polynomial with a factored expression structurally; that log is retained as `common_kernel_review-attempt01.log`, and the corrected check uses their expanded difference.

Let W be `k⊥` and let w be the orthogonal projection of the all-ones vector into W. Since `kᵀk ≠ 0`, W is nondegenerate and every symmetric matrix killing k restricts to a self-adjoint map of W. Moreover `T1=Tw`, `1ᵀw=wᵀw=s`, and the tangent condition is `wᵀTw=0`. The quadratic permanent coefficient restricted to this space is `tr(T²)-2(Tw)ᵀ(Tw)`.

If s is nonzero, choose an orthonormal basis of W with first vector `w/sqrt(s)`. The tangent condition sets the first diagonal entry of T to zero. In the remaining coordinates its quadratic is exactly

    2(1-s)(b²+c²)+d²+f²+2e².

Its Gram determinant is `8(s-1)²`. Therefore s different from one gives a nondegenerate quadratic on five variables and permits no isotropic three-plane. When s is one, its radical has dimension two, and the nondegenerate quotient has dimension three. Any isotropic three-plane must contain the entire radical. In original coordinates that radical is

    { w uᵀ+u wᵀ : u ∈ W, wᵀu=0 }.

For s=1, the vector `1-w` is a nonzero multiple of k, so this u-space is exactly `{u : Σu=0, wᵀu=0}`. Also `Σw=wᵀw=1`. These identities justify applying the generator's classification in the original coordinates; arbitrary orthogonal changes are used only to analyze the quadratic, never to assert permanent invariance.

In the chart `w0 ≠ w3`, the generator's two u-columns span the entire required u-space: the minor in coordinates 1 and 2 is `(w0-w3)²`. An independent Ryser expansion, rather than the generator's permutation sum, reproduces the complete saturated ideal

    [a²-a, h-2a+1, b, c].

Here `w=(a,b,c,1-a-b-c)` and `h(w0-w3)=1`. Its solutions are exactly w=e0 and w=e3. The omitted quadratic coefficients vanish modulo `wᵀw-1`, which the independent check verifies. Every admissible w has unequal coordinates somewhere: an all-equal w with sum one would have norm 1/4. A vertex permutation therefore puts it in the checked chart. The full classification is consequently w=ei, whose radical is precisely the standard star plane centered at i. The existing star nonextension obstruction applies.

If s=0 but w is nonzero, take w=(1,i,0) in an orthonormal coordinate system of W. The tangent equation is `d=a+2ib`, and the quadratic becomes

    2(a+ib)²+f²+4e²-4ice.

It has rank four on the five-dimensional tangent hyperplane, with radical exactly `span(wwᵀ)`. Every isotropic three-plane must contain that radical. This gives a nonzero symmetric rank-one direction, which cannot be constant-permanent: the coefficient of degree j in `per(J+t vvᵀ)` is `j!(4-j)! e_j(v)²`; constancy forces all elementary symmetric functions to vanish, hence v=0.

Finally, w=0 means k is proportional to the all-ones vector. All candidate matrices then have zero row sums, so the previously established row-sum-zero three-plane obstruction applies. No correction to the stated nonisotropic-common-kernel scope is needed.
