# Longer native full-star finite-field diagnostic

This run used the same independently verified full-star F1009 input as
`sparse-star/`, with all 31 equations in 18 variables. It used the separately
reviewed native AVX512/OpenMP neogb build, two threads, exact sparse linear
algebra option 2, all critical pairs per degree, a 600-second wall limit,
6 GiB address-space limit, and disabled core dumps. The wrapper also limits
aggregate CPU time to 1,202 seconds. Native-build controls and provenance are
preserved by the engine owner; exact binary/library hashes appear in the run
metadata.

The outcome was `UNKNOWN_TIME_LIMIT` after 600.295 seconds, with peak child
RSS 2,357,776 KiB. Nine algebra rounds completed. The first degree-six round
reduced a 46,990 by 120,229 matrix in 114.91 seconds, yielding 1,764 new basis
elements and 1,625 zero reductions. This led to one degree-four and three
degree-five rounds. The next degree-six batch, selecting 4,111 pairs, was
unfinished at the time limit. No basis or mathematical verdict was emitted.

The frozen `native-star-r1/` archive preserves the exact input and provenance,
full stdout/stderr, wrapper metadata, and wrapper source. This is a finite-field
computational diagnostic, not a characteristic-zero or Lean proof. A modular
unit basis, had one been obtained, would still require an exact QQ certificate.
