# L-gct-231 handoff · 25 November 2026

The desk returned HTTP 410 when the root agent renewed L-gct-231 at 13:07 UTC. The step had been withdrawn. Work on its mathematics stopped, and the desk assigned L-meta-3773 at 13:09 UTC. This archive preserves the unfinished research. **Neither the requested three-space nor a proof of its nonexistence was obtained.** The existing two-dimensional centered-star example is exact.

## Checked parts

The fork contains Lean-checked obstructions for the all-zero top-row branch (AllZeroGeneralObstruction.lean), a singular normalized direction and partner (ExceptionalSingularDirection.lean), repeated row-kernel cases, two-block cases, and the sparse-star case. The checked dense-star matrix constraints give isotropy for an explicit ternary quadratic and characterize its kernel; the file states the precise hypotheses. LaguerreBlockObstruction.lean proves the isolated-row quartic, and LaguerreRowKernel.lean relates the row kernels. These are conditional pieces of a larger argument. The checked files through fork commit 64b9c84a had already been preserved before this diagnostic archive.

## Remaining full-row problem

A full row projection gives an isolated-row anchor A=diag(λ,S₃). The quartic for λ and the three coefficients of the lower rook polynomial reduce the anchor family to three parameters. The first and second derivative equations then give a small common-direction resultant on the generic rank-five stratum. The derivation, scripts, data and failed raw elimination run are recorded in fresh_laguerre_diagnostics_manifest.json and fresh_laguerre_row.md. The rational-anchor censuses over primes 11 and 19 leave the algebraic-closure and characteristic-zero problem unresolved. The physical 17-variable F4 trial reached its address-space limit.

The rank-deficient diagnostic at prime 461 and λ=21 finds a unit ideal for jet rank at most three and a 276-dimensional quotient algebra for necessary rank-four compatibility equations. Its number of standard monomials counts the algebra, including multiplicities. Further slope constraints remain. The exact scope and inputs accompany geometry-laguerre-rank4-manifest.json.

## Four-frame and diagonal-anchor work

The localized frame Gram calculations are conditional on the stated nonzero normal and Gram-pairing assumptions. The path computation returned a rational unit ideal, the triangle computation returned a modular unit ideal, and the rational triangle computation hit its CPU limit. The coefficient-index bridge failed its assertion. The data are listed in frame-gram-localized-diagnostic-manifest.json.

The 361-digit Dixon files preserve a lifting state for the frame calculation. They did not produce a reconstructed rational identity. The final carry replay was outstanding when work stopped. Use three-plane-ordered-norm-final-archive-manifest.json to identify the exact snapshot.

For a diagonal anchor, two independent matrix constructions agree modulo 461 and give a nonzero exact integer moment determinant. The abstract plane-overlap lemma passed Lean. Four attempts to formalize the numerical moment-matrix endpoint hit memory or wall-time limits. Their statuses and exact matrices are preserved in three-plane-diagonal-final-preservation-manifest.json. This diagonal-anchor argument and the Cauchy-frame application remain mathematical and computational partial results.

A future proof would still need a characteristic-zero obstruction or a witness in the general full-row case and coverage of the remaining four-frame configurations. The combined preservation manifest binds the specific files and their SHA-256 digests.
