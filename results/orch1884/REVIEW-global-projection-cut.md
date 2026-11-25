# Independent review: GlobalProjectionCut

UTC: 2026-11-25T16:34:22.096219+00:00

Verdict: PASS for the conditional dependency helper. Source SHA256 `611940656f2d9362f02572810252eb801aa61faa27e34646a9e898d4d771d372`, 8283 bytes, 171 lines. Author reported Lean exit 0; complete archived global-projection-cut.stdout and .stderr are empty. No new compilation was run by this reviewer.

`projected_available_of_supply` covers literal membership, constants, and signed complements; the last case uses mode=true explicitly. `replay` transports every Reach constructor and preserves exact binary-step cost. `replay_skip_constant` removes precisely one explicit operation whose projected operand is constant; its operands remain supplied, and the generic constant simplifier preserves either binary operation.

`two_constant_cut` requires an explicit reached prefix, supplied retained roots, two distinct retained signatures, and vanishing of the additional signature under the chosen projection. It lists both distinct roots before the remainder to charge two constant roots, applies the already checked signed nine-variable floor15, and obtains the stated bound including the one separately counted operation. `one_constant_after_skipped_step` trades one skipped prefix operation plus one retained constant root for the analogous bound. The shown p/q/k arithmetic does not assert that an arbitrary syntactic circuit has the required split, retained roots, or projection property.

The only import is the scratch dependency TwoPrefixFloor, so this is not a standalone submission file. Its inherited Binary17 certificate and the already reviewed TwoPrefixFloor must be assembled under allowed imports for submission. Correct L_meta_1884 namespace; no options, forbidden constructs, new axioms, strings, unsafe declarations, or secret-like content. Below 512 KiB. These lemmas do not close L-meta-1884 and do not state a literal circuit fanout-one theorem.
