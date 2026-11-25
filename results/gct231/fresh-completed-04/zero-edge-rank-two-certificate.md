# A zero-edge pencil with diagonal rank two

This is a mathematical existence certificate using exact rational inequalities and the Banach contraction theorem. It is not Lean checked, and it is not a three-dimensional witness for L-gct-231. An independent review passed at 2026-11-25 11:21:04 UTC. It refutes the proposed auxiliary assertion that every normalized constant-permanent pencil with T01=x, T02=y, T03=0 must have diagonal projection rank at most one.

The twelve-variable polynomial system is `fresh/zero-edge-pencil.json` in scratch. Its variables are the x,y coefficients of T00,T11,T22,T12,T13,T23, in that order. The tangent equation eliminates T33. Its twelve equations are exactly the three quadratic, four cubic and five quartic coefficients of permanent(J+T(x,y))−24. The fixed offdiagonal entries x,y ensure that the pencil is two-dimensional.

A numerical search found a candidate with a nonsingular coefficient Jacobian. Four high-precision Newton steps gave a center z0 with residual approximately 3.44e−100. The saved decimal coordinates and approximate inverse Jacobian are interpreted as exact rational complex numbers in the subsequent certificate, so no floating-point result is used as a proof premise. The source data is `fresh/zero-edge-high-precision.json`.

Let F be the twelve coefficient polynomials and R the saved rational matrix. On complex coordinates use the norm |Re z|+|Im z|, and on vectors the maximum coordinate norm. Set r=10^−20. Exact rational evaluation and monomial derivative bounds verify:

* ||R F(z0)|| ≤ 2.254e−92.
* ||I−R DF(z0)|| ≤ 1.143e−72.
* On the closed radius-r ball around z0, the Jacobian variation of R F has Lipschitz bound M < 6,866,468.
* Therefore the map Φ(z)=z−R F(z) has contraction constant at most 6.867e−14 on that ball and maps the ball into itself.

The exact fractions, rather than these rounded summaries, are saved in `fresh/zero-edge-rational-certificate.json`. The executable certificate checks the strict rational inequalities η+Mr<1/2 and ε+(η+Mr)r<r. Since ||I−R DF(z0)||<1, the square matrix R is invertible. Banach contraction therefore gives a point z* in the ball with F(z*)=0.

The diagonal minor formed by rows0,1 is v0*v3−v1*v2. At z0 its real part is approximately −3.763170441785765. Throughout the certified ball its variation in the complex norm is at most 5.081e−20. Its real part consequently remains nonzero at z*. Thus the diagonal projection of the resulting pencil has rank two.

Complete sources/logs are `fresh/zero_edge_high_precision.py/.log` and `fresh/zero_edge_rational_certificate.py/.log`. The rational certificate completed in under one second after the high-precision data was generated. Earlier numerical fits that approached diagonal rank one are not used in this argument.

Agent `/root/fresh_main_proof/c3_review` independently recomputed every exact saved fraction using explicitly differentiated Hessian polynomials, rather than the author's monomial multiplicity loop. It also checked the matrix/polynomial lineage against the independent Ryser expansion and reviewed the norm, fixed-point, invertibility, and minor arguments. Its complete source/log is `fresh/zero_edge_rational_certificate_review.py/.log`, with exact values in `fresh/zero-edge-rational-independent-review.json`.
