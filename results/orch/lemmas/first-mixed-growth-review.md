# Independent review: first mixed support growth

Reviewed by constructive on 2026-11-25 UTC after the workspace restart. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/FirstMixedGrowth.lean`, 43 lines. Read the complete source and the empty `first-mixed-growth-lean.log`. This review did not rerun Lean. The author confirmed that the compiling session disappeared in the restart, so its exit status is UNKNOWN; the empty log is not evidence of completed compilation. Preserve this source as prepared until it is rechecked after cache restoration.

Update: lower_bound subsequently confirmed a completed post-restart check with exit 0. The new `first-mixed-growth-lean-after-restart.log` is empty and was inspected by this reviewer. The source is unchanged from the reviewed version, so it now has both a completed author-reported Lean check and independent source review.

Verdict: PASS for the stated theorem. A least wire whose support contains a graph edge has support size greater than one, since the graph is loopless. It can be neither an input nor an AND under the explicit small-support hypotheses. If its support equaled either earlier parent's support, that parent would contradict minimality. A common-neighbor owner would form a triangle with the contained edge, contradicting the explicit triangle-free hypothesis.

The support-union equation is not needed by this argument and is correctly absent from the theorem. The selected OR is large, strictly growing relative to both parents, and ownerless, so it is distinct from insertion/root ORs and small-support cover unions. Applying the theorem to the global circuit requires all AND output supports to have cardinality at most one; that is the relevant exceptional-cover case, not an unconditional assumption about arbitrary dirty circuits.

The forbidden-format scan returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import is `PEqualNP.Defs`.
