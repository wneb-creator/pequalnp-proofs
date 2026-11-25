# Independent Lean relabeling review

Reviewed source: `/tmp/oec/pequalnp-pilot-75/gct231/lean/Relabel.lean`.

SHA256: `9bb9c8fc68852fa9909c988a7c3dd6b8355229ffa0323b7e363d69abee640609`.

The independent compile completed with exit code 0 under the existing pinned Lean 4.36.0 toolchain. The complete stdout/stderr log is `/tmp/oec/pequalnp-pilot-75/gct231/lean/Relabel.review.log`; successful compilation produced no output. The source hash was saved before compilation in `Relabel.review.sha256` and verified unchanged afterward. The command, run from `/workspace/pequalnp-proofs/lean`, was:

    PATH=/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin:$PATH lake env lean /tmp/oec/pequalnp-pilot-75/gct231/lean/Relabel.lean

The definition is simultaneous relabeling by pullback along the inverse permutation. Both linearity fields hold definitionally. Symmetry follows by applying the original symmetry equation at the two inverse-permuted indices. Injectivity follows by evaluating an equality of relabeled functions at the forward-permuted pair. Permanent preservation correctly expresses the new matrix as a submatrix with both indices permuted, then applies the two Mathlib permutation invariance lemmas.

The file is suitable as helper material: imports are at the top; every declaration lies inside the permitted auxiliary namespace; there are no extra instances, executable commands, custom axioms, admitted proofs, or unsafe computation. It does not itself declare the final posted theorem and is not a complete submission.

The subsequently supplied `ConditionalParameterization.lean` was also read without edits. Its mathematical construction is correct: the selected-coordinate map is reordered by q, converted to a linear equivalence, inverted, embedded into the ambient matrix-function space, and relabeled by p. The orbit hypothesis and symmetry identify the canonical edge coordinates with the input coordinates. The three canonical patterns are the star (01,02,03), triangle (01,02,12), and path (01,12,23).

After coordinating exclusive access to the Lean compile slot, I independently compiled that conditional source with the same pinned command and obtained exit code 0 with no output. Its SHA256 is `23fffea59e4a4f1ff777ab0639aafe1fb71acee7b64dd2ec1702fb4084d1a661`, saved before compilation and verified unchanged afterward. Full log, hash record, and result metadata are `ConditionalParameterization.review.log`, `ConditionalParameterization.review.sha256`, and `ConditionalParameterization.review.result.json` in the same scratch directory.

The additional `candidate_canonical_parameterization` corollary in `ParameterizationAdditions.txt` was reviewed at source level. Its composition of the existing coordinate-chart theorem, the three-edge orbit theorem, and the conditional parameterization is mathematically sound. Its integration build is a separate check and is not asserted by this report.

The final additions were rechecked at SHA256 `7a1b5bc375917710bfedd442f6adde72a0668637af4d21fd49577df6aa3ab250`, and the source verdict remains PASS. The author subsequently reported a successful driver compile with empty output; that driver has SHA256 `c4ddb2a67e6664d76426dca0f1accf2d83a9d2a9b4c72c6f18494dafd08ca1d3`. I did not duplicate that driver compile. The driver is explicitly a scratch integration source; only its additions, placed inside the existing auxiliary namespace, belong in the final file.
