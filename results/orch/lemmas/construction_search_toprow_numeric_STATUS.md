# Reduced top-row numerical searches: no candidate found

These are floating-point heuristic searches, not proofs of nonexistence or exhaustive algebraic censuses.

Both searches use six reconstruction parameters for the three active-axis top-row chart, three coordinates of a full-support rank-one base matrix, and one power-form scalar. They evaluate all relevant homogeneous quartic coefficients through an invertible35-point interpolation matrix, retaining23independent residuals. The permanent derivative and symbolic reconstruction derivative provide an analytic Jacobian; comparison with finite differences gave relative errors7.4e-10 and1.5e-10. The mixed-sign model additionally checked that the twelve omitted quartic coefficients vanish numerically, with maximum error8.6e-15.

The all-positive pair-sign branch ran1000complex initializations in51.8seconds. Its best coefficient-residual norm was0.07966268234. The mixed-sign branch ran1000initializations in69.6seconds; its best norm was0.08047888544. Neither produced an approximate zero, including degenerate cases under the stated threshold. Real and imaginary parameter parts were bounded to[-5,5], so the search does not cover unbounded parameter values or excluded degenerate charts.

The scripts, complete output logs, summaries, and best parameter vectors are preserved. The best vectors are unsuccessful numerical minima and must not be presented as constructions. The underlying algebraic reconstruction is documented separately in fresh_top_row_factorization.md.
