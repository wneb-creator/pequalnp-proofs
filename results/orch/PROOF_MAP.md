# L-meta-5012 research checkpoint

The exact posted theorem is **not proved**. The branch is a preservation branch; no proof PR has been opened. `statement.txt` is the exact leased statement. The named file imports only `PEqualNP.Defs` and contains checked helpers inside the allowed namespace.

## Strongest integrated result

`lean/PEqualNP/Outside/L_meta_5012.lean` has 8633 lines. `normalized_two_junk_with_guarded_residual` proves that a hypothetical least circuit with exactly two junk gates can be normalized, preserving size and junk count, to TopForm and a lift fixed point with a guarded residual edge. `combined-build-04.stdout` records a successful named target build. `axiom-audit-15.stdout` reports only propext, Classical.choice and Quot.sound.

## Completed components

| Component | Frozen source in lemmas/ | Use and limitation |
|---|---|---|
| Actual pure-product operands and nesting | structural_residual_independent.lean; structural_operand_normal_form.lean | An unguarded residual edge forces independent junk gates and two pure products. |
| First-rung surgery | restriction_star_edges.lean | An earlier-wire clean replacement that lowers the changed signal pointwise, preserves its Ustar values, and leaves the other junk outside its cone contradicts the no-one-junk premise. |
| Stronger clean rewrite | restriction_clean_rewrite.lean | An available earlier-wire clean AND preserving true Ustar rows can replace the dirty gate; global pointwise lowering is unnecessary. The other junk must be outside the edited cone. |
| Leastness witnesses | restriction_essential_cross.lean; restriction_ustar_hit.lean | Under leastness, TopForm and a nonempty graph, every junk hits Ustar; a singleton-active junk also hits Ustar away from that singleton. |
| Geometric classification | pure_product_classification.lean | Pure product guarded edges have one-center, flag, or singleton-overlap alternatives. It does not supply actual circuit usage witnesses. |
| Residual cover | inventory_residual_split.lean | Covers edges outside clean-top edges and outside all junk-guarded edges with two stars and a splitting-OR budget. |
| Extra OR cost | inventory_independent_cost.lean; inventory_antichain_cost.lean | Explicit cover-cost criteria contradict leastness. Cover hypotheses still need to be established globally. |
| Guarded leaves | structural_guarded_mixing_antichain.lean; structural_guarded_mixing_strict.lean | Actual clean-top path witnesses inject fixed-junk guarded leaves into an OR antichain, leaving a strict extra credit in the stated case. |
| Reused stars | guarded_reuse_package.lean; guarded_reuse_exclusion.lean | Packages a cover reusing old tops; whole-Ustar coverage and reuse conditions are explicit caller obligations. |

## Remaining mathematical work

The unresolved step is a global guarded-plus-residual cover/cost argument, including actual paths through the other junk gate and the nested case. Mere acceptance of an edge by a junk gate does not imply the accepting output path uses that gate. Geometric one-star cleanup shortcuts fail on explicit nonleast examples. The saved counterexamples do **not** refute L-meta-5012.

## Verification and environment

The full local checker reports `CHECKER FAULT: the prebuilt Mathlib cache is missing.` The pinned Lean 4.36.0 toolchain and a selective prebuilt Mathlib cache support Defs and all saved successful partial builds. The full Mathlib umbrella required by the checker was unavailable within the container disk budget. No Mathlib source build, sorry, new axiom, or native_decide was used. The completed compiler checks do not establish the absent target theorem.

Each frozen source has complete stdout/stderr logs and independent review records. Some standalone helper files have namespace/section forms that must be normalized if incorporated into the final one-file PR. The named file has already passed its formatting scan. A final proof PR must have a one-file diff; this preservation branch also contains research artifacts.

The two longer normalized circuit searches were interrupted by an environment restart. They have no solver conclusion. Search evidence and unsuccessful shortcuts are separately identified in search/README.md.
