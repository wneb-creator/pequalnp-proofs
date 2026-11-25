# Independent review of reduced C4 cases 2 and 3

The frozen 46-file archive `reduced-c4-cases23/` passes independent exact coverage and SHA256 verification against manifest `f69462cd385f0026718b2a01e56969f3190680f7d72ac15039f5b62375203c90`. Every included file is regular UTF-8 text with no binary payload. The already-reviewed original reduced JSON hashes and normalized variable/equation lineage match.

All six polynomial rows in each of the four QQ/F1009 inputs were reconstructed independently from the source equations, including primitive integer scaling, variable order, sparse exponents, input hashes, and modular reduction. The two F1009 runs report completed nonunit bases of five independent affine linear polynomials. Their unique finite-field roots agree with the reductions of the exact rational points:

- Case 2, `(P,B,U,V,sat)=(-2,1,0,6,-1/26)`.
- Case 3, `(A,beta,U,V,sat)=(4,1/2,0,-12,1/13)`.

Direct rational substitution confirms all six original equations at each point. This does not classify all complex solutions, and the review does not turn the finite-field output into a characteristic-zero certificate. Both QQ runs remain `UNKNOWN_TIME_LIMIT` after 120 seconds, with no basis; neither is an exclusion result.

Both algebraic lifts of each displayed rational point violate the omitted necessary square-pencil condition (value −1 in the original expression). The augmented seven-equation systems are separate later inputs and are not part of this archive's solver verdict.

Standalone independent source and full log: `/tmp/oec/pequalnp-pilot-75/gct231/reduced_c4_archive_review.py` and `reduced_c4_archive_review.log`. Completed 2026-11-25T11:30:05.444359+00:00. No solver was rerun. Source derivation and boundary coverage have separate reviews in `c4-nonzero-reduction-review.md`.
