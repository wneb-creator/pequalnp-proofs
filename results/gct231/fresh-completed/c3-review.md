# Independent review of the C3-stable obstruction

Reviewer: `/root/fresh_main_proof/c3_review`. Completion recorded: 2026-11-25 09:55:56 UTC.

Verdict: the final section of `fresh.md` gives a valid exact symbolic argument excluding complex three-dimensional solution spaces stable under the permutation cycling vertices 1, 2, 3 and fixing vertex 0. This does not exclude arbitrary three-dimensional solution spaces and is not a Lean-checked result.

I reread the three named scripts and logs and reran `c3_invariant.py`, `c3_fourier.py`, and `c3_smooth.py`. Their stated outputs were reproduced. I also independently recomputed both permanent identities using Ryser's subset formula, rather than the scripts' permutation sum. Both identities agree exactly.

The invariant symmetric matrices have four parameters before the degree-one condition, and that condition is exactly `a = -6b - 3c - 6d`. The displayed quadratic, cubic, and quartic coefficients are correct. Since these equations are homogeneous, the charts `b = 1`, and then `b = 0, d = 1`, cover all directions with either b or d nonzero. Each chart has Groebner basis `[1]`. The remaining case `b = d = 0` has quadratic coefficient `-12c^2`, forcing c = 0. Thus no nonzero invariant direction is available.

For the action `(rho B)[i,j] = B[sigma(i),sigma(j)]`, with sigma = (1 2 3), the displayed character matrix satisfies `rho B = w B` modulo `w^2 + w + 1`. Its parameters u, v, q are independent. The characteristic polynomial of this action on the full ten-dimensional symmetric matrix space is `(z - 1)^4 (z^2 + z + 1)^3`; hence the matrix describes an entire nontrivial character space. The other character space is obtained by replacing w with its conjugate. The permanent identity is exactly `per(J + h B) = 24 + h^3 F(u,v,q)` with F as displayed in `fresh.md`.

The derivative ideals on `q = 1`, `q = 0, u = 1`, and `q = 0, v = 1`, together with `w^2 + w + 1`, each have Groebner basis `[1]`. These charts cover projective space. Alternatively, on q = 0 the two derivatives `F_u = 6v(u + v)` and `F_q = 6wu(u - v)` already force u = v = 0. Euler's identity for the homogeneous cubic shows that vanishing of all three derivatives is the projective singularity condition. The calculation treats both primitive roots w, so smoothness holds in both character spaces.

A smooth plane cubic over the complex numbers has no linear factor: if `F = ell Q`, the projective line ell = 0 meets the homogeneous quadratic Q = 0 (or is contained in it), and their intersection is singular for F. A homogeneous polynomial vanishing on a two-dimensional vector subspace is divisible by its defining linear form. Consequently neither nontrivial character space contains a two-dimensional vector subspace on which F vanishes identically.

Finally, a C3-stable complex subspace splits into its intersections with the three eigenspaces, since the action satisfies the squarefree polynomial `z^3 - 1`. A solution space cannot have any invariant component by the invariant-line calculation. If its dimension were three, one of its two remaining character intersections would have dimension at least two, contradicting the cubic calculation. No correction to the stated scoped conclusion is needed.
