# Sparse rational C4-support chart-zero diagnostic

The supplied rational Witt-chart JSON contains six parameters and 25
equations, with degrees up to eight. Its SHA256 is
`3ab6980d652d11bf784ad960b1e5e377bbadc1d858d82a2455956b2a97f3c2c9`.
The generator and mathematical chart analysis belong to the fresh proof
route. This diagnostic only tests the supplied equation list; it does not
independently establish chart coverage or a global permanent statement.

The separate Witt-schema converter clears denominators and primitive content,
producing 25 integer generators with 5,609 terms. A second parser reconstructed
every polynomial over QQ and compared it with its exact nonzero scalar multiple
of the source equation. The input SHA256 is
`d49c676b4edd368a24f476484d9cf9733307731a99af65670d718001414c678d`.

The validated serial neogb QQ wrapper used degree reverse lexicographic order,
exact sparse linear algebra option 2, all critical pairs per degree, a 120-second
wall limit, 4 GiB address-space limit, and disabled core dumps. It ended
`UNKNOWN_TIME_LIMIT` after 120.032 seconds, with peak child RSS 695,596 KiB.
Six degree-seven rounds completed in about two seconds; the next degree-eight
matrix had 1,843 rows and 2,746 columns and was still being reduced at the cap.
No basis or mathematical verdict was produced. This is not a Lean result.

The separate `sparse-c4-chart0/` archive preserves the exact source JSON, sparse
input, conversion provenance, roundtrip checker, full stdout/stderr, and wrapper
metadata. Engine source provenance and its bookkeeping patch are recorded in
the adjacent `sparse-engine/` archive; these runs predate SIMD/OpenMP builds.

An independent agent reconstructed every exact input equation and checked all
ten archived file hashes, exact manifest coverage, and the timeout status.
Its script and complete PASS log are preserved in `sparse-c4-review/`.
