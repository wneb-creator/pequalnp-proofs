# Reviewed at-most synthesis and signed-domination controls

The v7 model combines first-input-pair symmetry, adjacent independent-gate ordering, necessary positive/negative gate relevance and signed-separator domination exclusion before an exact target prefix. At-most mode exempts padding from operand-incomparability and domination/uniqueness constraints. The normalization note states the mathematical argument and its unformalized status. v5/v6 are source-only intermediate versions; no solver result uses them.

Three v7 controls passed SAT: fixed C5star7 padded to8slots (effective exact prefix7), fixed Petersenstar20 padded to21slots (prefix20), and unpinned C5star7. Independent replay checks all32/1024/32 assignments at both final output and earliest exact prefix, full ownership/cones and all pre-target signed-domination constraints. All guardian process groups are empty after normal completion.

No lower bound, full L-meta-2448 proof or counterexample is claimed. A nonstar redundant tail does not show that the effective prefix is nonstar; the decoder now reports both profiles.
