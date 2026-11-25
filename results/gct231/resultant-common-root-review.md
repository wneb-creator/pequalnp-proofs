# Fixed-degree common-root resultant helper

`resultant-common-root/ResultantCommonRoot.lean` compiles with the pinned Lean toolchain. It proves that two polynomials over a field sharing a root have zero resultant at any degree bounds m,n with m positive. The proof retains cases where either polynomial or its leading coefficient vanishes.

The exact source SHA256 is `7f6fb46d5724abb34a448d8ffdcb44adcbf2fa988ff1202bb6e8a86d62a7886c`. The final source run passed in 3.04 seconds and its axiom audit passed in 3.56 seconds, reporting only propext, Classical.choice and Quot.sound. All complete outputs, including the first failed closing simplification attempt, are preserved in the eight-file archive.

Independent source review by fresh_main_proof: PASS. The nonzero-polynomial branch evaluates a putative Bezout identity at the common root, then pads the degree bounds. The both-zero branch uses m positive to exclude the zero-dimensional resultant. No leading-coefficient assumption is hidden. This is a generic helper, not the posted gap theorem.
