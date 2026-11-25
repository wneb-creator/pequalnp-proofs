# Common isotropic plane coefficient corollary: integration review

The frozen `library/CommonPlaneCoefficientIdentities.lean`, SHA256 `1aaaa15f2afadc317c741261a7fb57dad2dc2f408c8c41726940c7568919e522`, passes independent source review. Byte comparison confirms the entire previously reviewed common-isotropic-plane proof and quartic-square coefficient proof bodies are preserved unchanged.

The final corollary assumes symmetry of two complex 4×4 matrices and a common two-dimensional subspace on which both quadratic forms vanish. The determinant pencil is q=det(N−XM). The proof rewrites the affine matrix X(−M)+N entrywise, uses the standard determinant-degree bound to obtain natDegree q≤4, obtains q=p² from the common-plane theorem, and applies the two coefficient identities.

There is no invertibility assumption on M or N, no requirement that q have degree exactly four, and no hidden nonzero-leading-coefficient assumption. Zero and lower-degree determinant pencils remain covered. This independent check did not run a compiler; the author's completed build is separate.

Review completed 2026-11-25T11:44:11.601715+00:00.
