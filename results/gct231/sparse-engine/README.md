# Sparse Gröbner research tool

Official msolve v0.11.0 commit cc044551f8e202d00691990fd3fd0b1226a88ea2 was cloned from https://github.com/algebraic-solving/msolve on 2026-11-25. The official INSTALL and configure.ac require GMP, MPFR and FLINT for the full executable. Only the independent neogb core target is compiled here, using GMP and libm; no FLINT, MPFR, autotools or external binary installation is used. The pristine clone is unchanged.

`neogb_cli` links the unchanged core. `neogb_cli_qqfix` links a separate derived core with the three exact bookkeeping edits in `qqfix.patch`. The original direct-rational path crashed because its linear algebra wrappers failed to update the metadata new-pivot count consumed by the subsequent basis update. The field-specific finite implementations update this count. ASan identifies the original crash in update.c:83; the full trace is preserved. The derived core updates it after both rational echelon wrappers and rational interreduction.

The patched core passes six controls: unit, nonunit, and rational-input systems over both QQ and F1009. Its returned reduced bases, normalized monic, exactly agree with independent Sympy Gröbner bases. Three unchanged-core F1009 controls also pass. These controls validate this interface on small examples; they do not independently validate arbitrary large Gröbner outputs.

## Run format

`python3 run_neogb_qqfix.py INPUT OUTPUT_JSON PREFIX --seconds 120 --memory-mib 4096 --pairs 0`

Input tokens: first nvars ngens characteristic totalterms, then ngens generator lengths, then one record per term containing numerator denominator and nvars exponents. Characteristic0 means exact QQ. Positive characteristic must be prime. Rational denominators are positive; coefficients must be nonzero (also modulo characteristic). Generators must be nonempty and have no repeated monomials; the converter must collect like terms. Exponents are nonnegative. Variables use the listed order and DRL.

The core runs serially with exact sparse linear-algebra option2, reduced-basis output, hashlog17 and configurable pair batch. No probabilistic linear-algebra option is used. The wrapper emits all polynomial terms. The bounded runner saves complete stdout/stderr, wall and CPU limits, 4GiB default address-space limit, core-dump limit0, exit status and hashes. A timeout or nonzero exit is UNKNOWN/error, never UNSAT. A nonzero constant basis element is reported only as a computational unit-ideal result. The runner records the binary hash; provenance.json additionally records linked shared-library and source hashes.

The core has modular trace learning/application functions, but these encode the algorithmic reduction schedule. No ideal-membership certificate exporter has been established. A unit basis from any field is not itself a Lean refutation; a finite-field unit basis also does not establish a characteristic-zero unit ideal. Exact identity certificates and Lean checking remain necessary.

Do not copy the vendor clone, derived vendor source tree, shared libraries or executables into the proof repository. Preserve the wrapper, small patch, provenance and diagnostic logs separately if needed.
