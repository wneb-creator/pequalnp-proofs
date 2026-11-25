# Adapted basis and common isotropic plane integration

The adapted-basis construction is complete. For a complex two-dimensional subspace W of functions on Fin 2 ⊕ Fin 2, it constructs a basis whose first two vectors lie in W and hence an invertible matrix with those first two columns in W. A complementary subspace has dimension two; the two finite bases combine through the direct-sum equivalence. Matrix nonsingularity follows from linear independence of the constructed columns.

Scratch source `adapted-basis/AdaptedBasis.lean` has SHA256 `490d6f557ea62c82aa6eebb0843e32c34c60af26d0c752661654b14df0159f3c`. Its complete successful build log is `adapted-basis/build06.log`, with sampled-RSS metadata in `build06.run.json` (exit 0, approximately 4.06 seconds, peak 3241960 KiB). Earlier failed attempts remain as diagnostics; the successful source uses targeted imports and the existing pinned Lean toolchain.

The combined `library/CommonIsotropicPlane.lean` has SHA256 `ddd00bd47c8437801018a3ecb47e1929f2527ad63efdfd88ee328ed611838756`. Independent byte comparison confirms both adapted-basis theorem bodies are preserved exactly; only their surrounding namespace changes. The final theorem obtains the invertible matrix from the dimension hypothesis and applies the previously reviewed quadratic-column bridge. Its hypotheses are precisely symmetry of M and N, dimension two for W, and vanishing of both quadratic forms on W. It concludes that det(N−XM) is a polynomial square. There is no unproved adapted-basis hypothesis.

The independent integration source and complete log are `adapted-basis/integration_review.py` and `adapted-basis/integration-review.log`, under `/tmp/oec/pequalnp-pilot-75/gct231`. They record source hashes, successful author-build metadata, and the exact comparison. This review did not duplicate the combined Lean build and does not re-audit the preceding determinant-square bridge.

Review completed 2026-11-25T11:33:10.760004+00:00. This is an auxiliary geometric theorem; it does not resolve the original permanent problem.
