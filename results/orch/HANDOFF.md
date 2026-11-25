# L-meta-3451 partial-results handoff

The posted theorem remains unproved and unrefuted. No proof PR has been opened. This branch preserves checked partial results and research evidence; it is not a single-file proof submission.

## Checked Lean results

The single main source is `lean/PEqualNP/Outside/L_meta_3451.lean`. Its helper namespace is `PEqualNP.Outside.L_meta_3451_aux`. At this checkpoint it has 3662 lines and SHA-256 `4a0687272d92a47f45a32d19edf41cf9ecee5a89eb59af23dfc54e0b471f7a2f`.

- `Two.normalize`: the full normalization conclusion for every two-by-two relation, with no C4 hypothesis needed. The lower bound uses a kernel-evaluated finite certificate and a proved circuit-enumeration soundness theorem.
- `Support.normalize_supported`: arbitrary ambient N when all incidences lie on two selected points and two selected lines.
- `Star.point_star` and `Star.line_star`: arbitrary-size stars.
- `Small.normalize_three`: the full conclusion for all circuits with at most three gates, for arbitrary N.
- `Bridge.pair_iff_full`: pair rejection alone, universally quantified over all N, is equivalent to the exact posted statement. This is an equivalence, not a proof of either side.
- `Prune.edge_active_normalization`: simultaneously zero every AND unused by all positive edges, preserving exact semantics and size.
- `Prune.edge_sensitive_normalization`: choose a globally size-minimal equivalent circuit in which zeroing any AND destroys some positive edge. This does not assert the required rejection conditions.
- `Surgery.contextual_same_function`: a cost-neutral mixed-centre rewrite under explicit full-negative-input domination and continuation-use hypotheses.
- `SingletonFormula.normalize`: singleton-clean normalization for positive formulas with no larger leaf count. It does not cover shared circuits.
- `Dependency`, `Boundary`, and `Restriction`: general support bounds, complete boundary testing, and input substitution lemmas used above.

All 282 declarations in the final compiled main file were audited with Lean `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur. The complete audit is in `axiom-*`.

## Validation and limits

Named build: `lake build PEqualNP.Outside.L_meta_3451`, from `lean/`, succeeded. Complete stdout/stderr are preserved as `build-edge-sensitivity.*`. The project uses Lean 4.36.0. The task fetched prebuilt caches and did not run `lake update` or build Mathlib from source.

Official `tools/check-lean.mjs`: infrastructure FAULT, exit 3, because the full prebuilt Mathlib cache is missing and does not fit in the container. Complete checker stdout/stderr are preserved in `checker.*`. The source format guard separately reports the missing full theorem; this partial file is not accepted or PR-eligible. Cleanup was skipped because the official checker could not run. Line count before/after skipped cleanup: 3662/3662.

Independent reviews cover the exact source, public metadata, finite-search encodings, verdict accounting, and stored witnesses. The C6 LRAT/CNF pair has been checked for integrity and structure only; it is not Lean-verified.

## Unresolved mathematical step

The remaining issue is a size-preserving global rewrite for shared circuits. Edge activity and positive-edge sensitivity do not force clean ANDs. Explicit inefficient P4 and two-matching examples show that local zeroing or choosing one factor cannot suffice; coordinated changes to gates and their readers are needed. A local rewrite has been proved, but exposing suitable contexts in every minimum-size circuit remains open here. Pairwise domination cannot replace domination on every negative assignment: higher-order independent sets matter.

A possible counting route would prove separate OR and AND resource lower bounds and then use a clean star-cover construction. Neither general lower bound was established. Ordinary matrix rank already loses information on C8.

## Computational evidence

The reviewed frozen four-by-four census covers 25 essential graph classes: 14 solver UNSAT results at one below verified clean upper bounds, 11 UNKNOWN results, no SAT counterexample. All 359 stored clean witnesses were independently replayed. The encodings represent circuits of at most the budget; repeated-operand OR copies give the required padding. These results are computational evidence, not Lean proofs. Interrupted runs are recorded without a verdict.

See `NOTES.md`, `TIMELINE.md`, `review-computational-evidence.md`, and `counterexample-review-manifest.json` for precise scopes and complete logs. Later long-search results, if any, are recorded separately and must not be inferred from this frozen census.

The desk sketch asks for a decomposition, but the public row lacks `reductions: true`; the global reductions switch alone does not authorize a reduction for this step. No reduction was submitted.
