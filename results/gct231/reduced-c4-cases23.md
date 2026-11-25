# Reduced C4 cases 2 and 3

These are computational results for two necessary polynomial systems on the nonzero-scale, nonzero-determinant C4 stratum. They are not proofs about the complete L-gct-231 statement. The input derivation was independently reviewed in `fresh-completed-04/scratch/fresh/c4_nonzero_reduced_review.py` and its complete log.

Each system has five variables and six equations. Serial native sparse elimination over the finite field of 1009 elements completed with a nonunit basis of five linear polynomials:

| Case | Ordered variables | Rational lift of the finite-field point | Wall time |
| --- | --- | --- | --- |
| 2 | P, B, U, V, sat | -2, 1, 0, 6, -1/26 | 0.116301 s |
| 3 | A, beta, U, V, sat | 4, 1/2, 0, -12, 1/13 | 0.068077 s |

The saved exact substitution script independently verifies that these rational points satisfy all six original rational equations. This is an existence check for the reduced necessary systems. It does not establish that these are their only complex solutions. Both points fail a further necessary square-pencil condition, as recorded independently in `fresh-completed-04/scratch/fresh/c4_reduced_root_obstruction.py` and its log.

Two serial exact-rational attempts, each bounded at 120 seconds and 1 GiB with pair-selection parameter 32, ended without a basis: case 2 after 120.035377 seconds (421084 KiB maximum RSS), case 3 after 120.030656 seconds (490604 KiB). Both are UNKNOWN, not nonexistence results. The pair parameter can be exceeded by equal-LCM boundary ties.

The 46-file `reduced-c4-cases23/` archive preserves source systems, exact input conversions, preflight checks, full solver logs and metadata, finite-field bases, and rational-root checks. Its manifest SHA256 is `f69462cd385f0026718b2a01e56969f3190680f7d72ac15039f5b62375203c90`. The separately saved U=0 factorizations are conditional algebraic observations only; U=0 has not been proved over the complex solutions.
