# Independent OneGateAfterNot review

Verdict: PASS for the functional bypass lemmas and preservation. No circuit-index or gate-deletion theorem is claimed by this file.

Reviewed source: `lemmas/OneGateAfterNot.lean`,43 lines,1582bytes. SHA256 `66aa99ab9c10d17f6b11981f939167367098c398fdf627805b472eccaef17e15`. Complete copied compile logs `one-gate-after-not-checked.stdout` and `.stderr` are both empty; the author reports exit0.

For an increasing Boolean h on a partial order with a top element, the hypothesis that `!h AND a` is true at the top forces h to be false everywhere. The expression therefore equals a everywhere. The dual bottom-element hypothesis for `!h OR a` forces h to be true everywhere, with the same conclusion. The proof uses only those endpoint values and monotonicity of h; no unstated monotonicity assumption on a is needed.

The two fiber corollaries apply these arguments separately for each fixed value of the distinguished Boolean coordinate. The remaining nine inputs carry their ordinary pointwise Boolean order, whose top and bottom are the all-true and all-false assignments. The source does not assert that an arbitrary circuit prefix supplies the required monotonicity, that the NOT is in a particular gate position, or that bypassing it removes a counted gate; those are separate structural obligations.

Only PEqualNP.Defs is imported. The namespace is correct, and the source has no options, attributes, string literals, forbidden root qualifier, additional axioms, sorry, native_decide, unsafe code, credentials, or binary content.
