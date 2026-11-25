# Corrected C4 coordinate and coefficient interface

The standalone deliverable helper source is C4CoordinateInterfaceFull.lean, SHA256 22de414e9c8b8b992ce11a46d8167da4f09d86ddafc71f29e7bbd84317e317fe. It compiled with the pinned Lean4.36 toolchain, exit0, empty final build log, 14.73 seconds and 2,675,068 KiB peak RSS. Independent source review passed.

It defines the corrected seven-parameter symmetric C4-supported tangent matrix, proves the exact permanent expansion, identifies the degree-two and degree-three univariate polynomial coefficients as Q4/4 and C16/16, derives their vanishing from constant permanent along a line, and proves the e=0 product identity f*a*b=H*X*Y. Its reconstruction theorem covers every symmetric 4×4 complex matrix with entries02=13=0 and total entry sum zero.

The intermediate integer-scaled matrix 8T is used only to simplify the exact ring calculation. The full source restores T=scaledMatrix/8. All hypotheses remain explicit; this does not assert that an arbitrary candidate three-plane has C4 support, nor does it prove nonexistence of a C4 three-plane or the original existential target.

C4CoordinateInterfaceAudit.lean is an audit-only copy with print commands and is not a deliverable. The raw reconstruction and quartic helper sources record the independent child's contribution. Earlier failed build logs are retained: missing local time executable, unsuitable virtual-memory limit, incomplete matrix simplification, and corrected evaluation imports/simplification. The final source and empty build03 log are authoritative.

The axiom audit completed successfully for coefficient_formulas, product_identity_of_constant_line, and scaledMatrix_reconstruct_supported. Each depends only on propext, Classical.choice, and Quot.sound. The audit replay took14.76 seconds with2,677,972KiB peak RSS.
