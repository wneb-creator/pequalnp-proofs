Checked sparse-star obstruction, research partial for L-gct-231.

SparseStarSubmoduleComplete.lean proves that a three-dimensional complex symmetric matrix submodule on which permanent(J+T)=24 cannot contain the star with edges (1,-1,0). It also proves the corresponding obstruction for any linearly independent matrix triple containing that star. Every proof is contained in this source; there are no remaining callback assumptions.

Validation: pinned Lean exit 0, 60.0148 seconds, peak aggregate RSS 2924441600 bytes, under a 4GiB / 120 second monitor. Full stdout/stderr and run metadata are included. The source contains the previously checked ProjectiveNormalization and SparseStarPairedMatrix foundations, plus explicit finite-sample polar extraction, a linear gauge change, scalar affine-plane case analysis, and basis extension.

The accompanying Python/SymPy polar expansion is an independently executable CAS derivation, not itself Lean validation. The Lean source checks its three required coefficient identities directly from permanent evaluations. No global proof or refutation of L-gct-231 is claimed; the posted-statement checker does not apply to this auxiliary theorem.
