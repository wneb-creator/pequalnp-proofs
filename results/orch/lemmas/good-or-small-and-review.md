# Independent review: small AND support edge budget

Reviewed by constructive on 2026-11-25 UTC. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/GoodOrSmallAndBound.lean`. Compared the complete diff against the previously reviewed `GoodOrGrowthBound.lean`. The accompanying compiler log is empty; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS for the stated refinement. Besides namespace and theorem renames, the sole hypothesis change replaces empty singleton support at every AND with support cardinality at most one. Its only use remains the local exclusion of an AND at a node whose owner-filtered support has cardinality greater than one. The new arithmetic contradiction is exactly sufficient there. All other hypotheses and proof steps are unchanged.

In particular, the cross-support adjacency hypothesis remains required at every AND. This helper does not independently justify treating a dirty AND as an ordinary edge-birth root; that bridge remains a separate obligation.

The forbidden-format scan returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import remains `PEqualNP.Defs`.
