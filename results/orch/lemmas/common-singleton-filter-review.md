# Independent review: common singleton filters

Reviewed by constructive on 2026-11-25 UTC. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/CommonSingletonFilter.lean`; 35 lines. The accompanying compiler log is empty; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS for both stated lemmas. `twoCommonPoints_filters_unique` uses two distinct points common to A and B to obtain all four cross-relations to any two points drawn from the entire filter family. The rectangular C4-free hypothesis then forces those filter points equal. The conclusion handles different filters and empty filters without additional assumptions.

`twoPoints_extra_noOwner` first forces any common-neighbor owner q of A to equal p, using two distinct members of A that are neighbors of p. The member of A that is not a neighbor of p then gives the contradiction. The relation orientation and equality substitution are correct; symmetry and irreflexivity are not silently assumed.

The source contains no forbidden `_root_` identifier, string literal, attribute, option, `sorry`, new axiom, or `native_decide`. Its standalone `Mathlib.Init` import must not replace the assigned gap's posted import block when integrated. These are local structural lemmas, not a complete gate-count lower bound.
