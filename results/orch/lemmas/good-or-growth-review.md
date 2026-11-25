# Independent review of GoodOrGrowthBound

2026-11-25 UTC. Reviewer: constructive. Read-only review; no compilation, desk call, or git action.

Verdict: PASS for preservation as a checked partial helper. This is not a proof of L-meta-2732 or of a one-dirty-gate lower bound.

Reviewed `/tmp/oec/pequalnp-pilot-70/lower-bound/GoodOrGrowthBound.lean` (229 lines), its full diff against the previously reviewed `GoodOrEdgeBound.lean`, and the complete empty `good-or-growth-bound-lean.log`. The author reports compilation exit zero; this reviewer did not rerun Lean.

The only mathematical change is the smaller paid OR set: in addition to having support larger than one and a common neighbor, the output singleton support must differ from both predecessor supports. In the local union-DAG step, equality with either predecessor selects the unary alternative, using the already established equality between F-support and singleton support at that predecessor. Both predecessor wire indices are strictly earlier. When neither equality holds, the proof supplies both inequalities and the existing common-neighbor witness to place the OR in the paid set. The covering, C4-free, AND-support, and graph hypotheses are unchanged.

Thus an OR which merely introduces old clean-edge terms into an existing singleton support is correctly excluded from this edge-growth budget. The theorem does not automatically convert that exclusion into a cover-number credit; that global step remains separate.

The file imports only `PEqualNP.Defs` on its first line and uses the allowed fully named helper namespace. No forbidden `_root_` text, string literals, attributes, options, `sorry`, new axioms, `native_decide`, or `unsafe` commands were found. There are no extra type or instance declarations. Its four theorem declarations are the inherited union helpers, the strengthened edge bound, and the mixed-support no-owner lemma.
