# Unverified P4 clause-bridge drafts

These exact sources are archived while their Lean builds are still running. **No theorem result or circuit lower bound is claimed from these drafts.** The full 2537-clause encoding bridge is attempted both as one proof and as independent 100-clause chunks. They encode the same concrete CNF whose UNSAT has already been checked separately by the trusted LRAT replay. The previously checked IR, direct evaluator semantics, and operand-order normalization remain separate established artifacts.

The `ReductionsNoFive.lean` composition draft depends on the unfinished full bridge. It has not been compiled. A completed version would only exclude exact-five typed P4 circuits with distinct inputs and final output wire8; it would not prove the eight-input double-star lower bound, an arbitrary actual-Circuit transport lemma, or L-meta-2602.

The `.snapshot.gz` files are explicitly in-progress snapshots, not complete final compiler output. Full original output continues accumulating in the job scratch logs. They will be refreshed or supplemented when the processes finish. Generation scripts and the full expression/clause trace are preserved, together with hashes of their already archived dependencies.

Build each module via the job Lean4.36.0 `lake env` in the repo `lean/` directory with the job scratch directory prepended to LEAN_PATH, using `lean --root /tmp/oec/pequalnp-pilot-64 -o /tmp/oec/pequalnp-pilot-64/MODULE.olean /tmp/oec/pequalnp-pilot-64/MODULE.lean`. IR and trusted-certificate modules must be compiled first. These are research drafts, not Outside PR files.
