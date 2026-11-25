# Isolated vertices have zero diagonal

The Lean theorem `IsolatedVertex.isolated_vertex_diagonal_zero` proves: for any complex symmetric 4×4 direction M and any vertex v, if every off-diagonal entry incident to v vanishes and `per(J+zM)=24` for every complex z, then M(v,v)=0. A separate tangent hypothesis is not needed.

At vertex 0, write M as the direct sum of d and a symmetric 3×3 block A. Let s be the sum of the entries of A, r the sum of its 2-rook products, and p its permanent. The four coefficients of `per(J+zM)−24` are L=6(s+d), Q=2(r+sd), C=p+dr, and F=dp. Evaluations at z=1,−1,2,−2 give L=Q=C=F=0. The exact identity

`d⁴ = −F + d*C − d²*Q/2 + d³*L/6`

then forces d=0. Simultaneously permuting rows and columns by the swap of 0 and v gives the arbitrary-vertex statement. The symmetry hypothesis supplies the opposite incident entries; the permanent is preserved by the standard row and column permutation lemmas.

Frozen scratch source: `/tmp/oec/pequalnp-pilot-75/gct231/isolated-vertex/IsolatedVertex.lean`, SHA256 `46ca6e535347b18b674028d70744585b63112c7e0c98eb6b6479614c59644470`. `IsolatedVertexAdditions.txt` contains the exact namespace body for integration, including the existing perm4 proof copied into this local namespace. No named source was edited.

The pinned Lean 4.36.0 build passed with exit 0 in 4.063 seconds, peak sampled RSS 3120660 KiB, under a 120-second / 5120-MiB sampled-RSS limit. The complete compiler/profile log is `build01.log` and the run metadata is `build01.run.json`. A separate exact Ryser check verified the block expansion, all four evaluation weights, and the d⁴ identity; its source/log are `algebra_review.py` and `algebra-review.log`. All source and log hashes are recorded in `frozen.json`.

Frozen 2026-11-25T11:45:19.825875+00:00. This is an auxiliary structural theorem; it does not settle existence of a permanent-constant three-plane.
