# Full-star center-diagonal coordinate change: independent review

The export `star-full-center-eliminated-equations.json`, SHA256 `845a45f7e3374b691dc8ef76eacf59938118b7961360c99d09505559c2e39f17`, passes independent review against the original full-star grouped source, SHA256 `a6a49ab3dab78f0c32da78838e91b0e1d3e722406d0607ee1bcc265d62790722`.

For each direction i, replacing the old diagonal00 coefficient d_i by `−(n_i+d_(i+3)+d_(i+6)+2(1+o_i+o_(i+3)+o_(i+6)))` is an invertible affine substitution. The same expression with d_i in place of n_i gives the inverse. Every matrix entry and all 31 coefficient equations were checked in both directions. Diagonal33 becomes n0*x+n1*y+n2*z; the symmetry, total-entry-sum constraint, and fixed star pivots x,y,z remain valid.

An independent Ryser permanent computation reconstructs exactly the 31 exported degree-two-through-four coefficients, totaling 3600 terms, with no constant or linear residue. Both actual sparse QQ/F1009 inputs were checked coefficient by coefficient, including variable order, primitive scaling and hashes. Their hashes are `f962797d0daa4ddc6167aba4625804cd6d9b85323a3fca139d6fe25f744686ff` and `2fa7c351ed1936e1f692cf06eb791c812748653e5e96ef76f0d0048ef7c864f6`.

The standalone reviewer source/full log are `/tmp/oec/pequalnp-pilot-75/gct231/star_center_elimination_review.py` and `star-center-elimination-review.log`. Completed 2026-11-25T11:47:16.656600+00:00. This is an equivalent 18-parameter chart, not a dimension reduction or solver outcome.
