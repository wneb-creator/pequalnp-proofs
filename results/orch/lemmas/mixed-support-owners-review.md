# Independent review of MixedSupportOwners

2026-11-25 UTC. Reviewer: constructive. Read-only review; no compilation, desk call, or git action.

Verdict: PASS for checked-partial preservation. Reviewed all 32 lines of `/tmp/oec/pequalnp-pilot-70/lower-bound/MixedSupportOwners.lean` and the complete empty `mixed-support-owners-lean.log`. The author reports compilation exit zero; this reviewer did not rerun Lean.

Given both centers in A and acceptance of their pair by B and S, loop rejection prevents B and S from selecting the same center. The proof therefore obtains the two possible opposite assignments, with the required non-memberships. Each common-neighbor conclusion is a direct use of `safe` on the fixed center and an arbitrary member of the opposite support. The argument does not assume symmetry, triangle-freeness, C4-freeness, or distinct centers without stating them; none is needed for this proposition.

No forbidden `_root_` text, strings, attributes, options, `sorry`, new axioms, `native_decide`, or `unsafe` commands were found. The standalone helper imports `Mathlib.Init`; final proof integration must preserve the posted import block rather than copying this helper import. This theorem supplies local ownership and does not settle circuit gate accounting or the posted existential statement.
