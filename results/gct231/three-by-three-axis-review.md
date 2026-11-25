# Rational obstruction for the normalized 3×3 coordinate-edge pencil

The displayed symmetric pencil has off-diagonal entries x,y,kx. The y-direction isolates vertex 0, so its diagonal coefficient vanishes: for an arbitrary 3×3 isolated-vertex direction, the checked identity is `d³=C−dQ+d²L/2`. The tangent equation then gives precisely the displayed eliminated last diagonal.

Independent Ryser computation verifies the four exported equations in `triangle_concept/three-by-three-axis-qq-equations.json`, SHA256 `01cce9a30fd640a2e625d5cbfd5018f9023d7f97c27c19cef83374c65ad1222c`. The pure-y equation is `q=s²+2s−1=0`. The mixed quadratic has r-coefficient `−2(s+1)`. Since `(s+1)²=2` on q=0, this coefficient is nonzero over C; eliminating r by the recorded substitution is legitimate. All retained primitive remainders, discarded zero remainders, three-variable order and 34 terms match exactly.

An independent bounded rational linear-algebra calculation found explicit multipliers h0,…,h3 with `Σ hi*fi=1`. Their total degree bound is seven, and they contain 18,7,18,10 terms respectively. Direct exact polynomial expansion verifies the identity. Thus the exported necessary system is inconsistent over C, without relying on the author's Gröbner-basis output. The unsuccessful degree-at-most-six certificate attempt is retained separately; it makes no mathematical nonexistence claim about certificates.

The rational certificate is `triangle_concept/three-by-three-axis-independent-unit-certificate.json`. Full independent source/log are `three_by_three_axis_review.py` and `three-by-three-axis-review.log`, completed 2026-11-25T11:56:55.183885+00:00. Clearing denominators gives integer constant 4214784; the source-only Lean candidate `ThreeByThreeAxisCertificate.lean` encodes that identity with `linear_combination`. It has not been compiled by this reviewer.

The conclusion is confined to this displayed normalized coordinate-edge pencil. Applying it to an arbitrary 3×3 pencil or a center-star rank stratum requires a separate chart-coverage argument. This review does not make that broader claim or a Lean proof claim.
