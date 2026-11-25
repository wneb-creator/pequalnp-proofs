# Independent review: StrongRelaxRows

UTC: 2026-11-25T16:39:44.746791+00:00

Verdict: PASS. Exact source SHA256 `3bda1221519d8d56b87e7b49203522274a04eaf113cb9b2d31906b9c2d07e314`, 3297 bytes/85 lines. The author reported Lean exit0; complete strong-relax-rows.stdout and .stderr beside the source are empty. This reviewer did not rerun Lean.

The specification contains12 positive edge rows and13 negative rows: the11 original nonexceptional maximal-independent rows plus21 and273. It does not include the optional stronger negative260 constraint. Therefore the lemmas apply to the25-row loose specification.

Three kernel-checked finite facts cover all positive inputs by a positive row below them, all negative inputs by one of the13 negatives or277 above them, and every negative input with coordinate2 or8 false by one of the13 negatives above it. Independent Python enumeration verified all512 inputs, both coordinates, and the signs of every listed row. The general lemmas use only explicit monotonicity of G: true values pass upward and rejection passes downward. Hence exact_cofactor proves exactness on either specified false cofactor; exact_if_exception_rejected proves exactness everywhere if277 is also rejected. No circuit or size hypothesis is implicit.

Only PEqualNP.Defs is imported. All six numeric option lines are scoped immediately above their finite declaration. Correct L_meta_1884 namespace, below512KiB, no forbidden constructs, new axioms, native_decide, unsafe declarations, string literals, attributes, or secret-like content. This is a row-to-semantics bridge, not an auxiliary circuit lower bound or the posted L-meta-1884 theorem.
