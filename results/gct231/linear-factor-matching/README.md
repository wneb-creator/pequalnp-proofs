# Binary linear-factor matching

The standalone source LinearFactorMatchingFull.lean compiles with the pinned Lean4.36 toolchain. Its final theorem binaryLinear_three_factors_match represents each form by a coefficient vector Fin2→ℂ and proves that equality of two triple products gives a permutation of the three factors and nonzero scalar multiples whose product is one. It explicitly assumes nonzero coefficient vectors for the first two left factors and all three right factors; nonzeroness of the remaining left factor follows from the product equality.

The proof evaluates at the kernel vector of a left form, uses the complex and polynomial integral-domain properties, and performs explicit cancellation. No unique-factorization classification theorem is assumed. The axiom audit reports only propext, Classical.choice and Quot.sound.

LinearFactorMatchingAudit.lean is an audit-only copy containing a print command; it is not a deliverable. The earlier standalone sources preserve the first-factor and two-factor milestones. The first build log records two corrected elaboration issues; the final build logs are empty and exited0.

This is a helper for the C4 case argument, not a proof of the posted existential three-plane statement. Independent root review remains required before integration.
