Independent review by lower_bound — PASS

Reviewed `lemmas/LeastGateFacts.lean`, SHA256 `7e648c34b04364a693513f7bc3a6ced2f05d1a3ea8b0f3dbb23d4482f863ddd3` (60 lines, 2755 bytes), against the definitions and specifications in `PEqualNP/MetaComplexity/Helpers/LiveSize.lean`. The author reports Lean exit 0; this review did not repeat compilation.

- `live` uses global minimum size among all Monotone2 realizations of the same full n-input function. An unread non-output gate can be removed by `delU`, which preserves AO2 and the function and reduces length by exactly one. The argument does not confuse mere local irreducibility with global leastness.
- `post_reader` uses ReadsBack to make the reader strictly later than the selected gate, then correctly translates its index into the suffix after that gate.
- `output_not_and_reader` uses the explicit true edge assignment row3, whose input2 is false. Any AND directly reading input2 is false on this assignment, so it cannot be the output. Correctness is required only on the input2=false cofactor, exactly as used.

No semantic weakening, unstated graph assumption, forbidden declaration, unsafe option, string literal, or forbidden namespace text was found. This is a helper importing other checked helper modules; it is not a standalone final proof of the posted gap.
