# Completed conceptual calculations for L-gct-231

This archive preserves scoped mathematics and exact symbolic computations.
Nothing here is a Lean proof, a complete solution of L-gct-231, or a global
nonexistence result. Sources and complete logs are copied without edits;
`PROVENANCE.json` records their original paths and hashes.

`concept.md` and `hidden-linear-symmetry/` establish that the identity component
of the linear stabilizer of the stated graded constraint ideal is scalar.
The exact 46-by-46 nonzero integer minor and separate rook-coefficient checks
are preserved. This rules out the proposed useful connected linear symmetry
at the fixed basepoint; it does not rule out the requested three-plane.
The original stalled generic-rank attempt and unsuccessful invariant ansatz
are retained with their full logs. They supply no positive mathematical
verdict; the fast matrix calculation and exact minor verification are the
successful route.

`zero-diagonal-classification.md` contains the complete UFD classification of
zero-diagonal solution two-planes into the 24 listed families. The argument,
including both degenerate cases, received independent mathematical review by
fresh_main_proof. `zero-diagonal-classification/` contains the independent
Ryser formula check and its full output. The initial check's incorrect
quadratic normalization assertion is preserved in the failed log; the final
successful log is `verify_formulas-v2.log`.

Combining this classification with the separately reviewed nonextension of
the 24 families implies that any solution three-plane has diagonal-coordinate
projection rank at least two. The nonextension checks are preserved with the
fresh worker's completed results; this archive does not claim to reprove them.
Rank-two and rank-three diagonal projections remain open.

The two nested `source-sha256.json` files are the original scratch manifests,
renamed only to distinguish them from this archive's `sha256.json`. The latter
covers every regular archive file other than itself. No vendor source,
binaries, or large traces are included.
