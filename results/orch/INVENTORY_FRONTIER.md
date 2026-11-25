Updated 2026-11-25T20:13:40.427092+00:00

# Pilot 176 inventory proof frontier

Status: partial results only. No proof of L-meta-5012 has been obtained by this agent.

## Exact cost interfaces now checked

1. `inventory_independent_cost.lean`, namespace `PEqualNP.Outside.L_meta_5012.Surgery`, final `independent_cover_budget_exclusion`: under leastness, LiftFixed, nonempty graph, NoFourCycle, exactly two ordered independent junk gates, an actual star cover of **all Ustar** with total leaves plus centers at most `splitExtra.card + 3` is impossible. The split filter is written explicitly in this Surgery file. Positive centreless count uses master surgery; centreless zero uses two distinct nonsplitting OR gates.
2. `inventory_antichain_cost.lean`, same namespace, final `guarded_antichain_cover_exclusion`: under leastness, LiftFixed, nonempty graph, NoFourCycle and two ordered junk gates, an actual all-Ustar star cover costing at most `splitExtra.card + A.card + centreless.card + 2` is impossible if `A` is an OR-antichain of raw-nonempty nonsplitting extra OR gates all reaching the **earliest** junk. Independence is not required. `inventory_unused_mix.lean` proves the unused nonsplitting OR needed when centreless is empty. Structural agent's fixed-g guarded mixing antichain has exactly this interface.
3. `inventory_residual_split.lean`, namespace `...MutualBudget`, final `residual_star_coverSplit`: covers only `Ustar \ coveredByJunk`, with total leaves plus centers at most `splitExtra.card + 2`. It does **not** cover guarded edges. `inventory_residual_bounded.lean` gives the earlier-index version using extra ORs before a cutoff containing both junk indices. Root has composed the latter with late mixing to exclude `Disjoint Ustar coveredByJunk`.

All these files were directly compiled and independently reviewed. Generic cover-cost lemmas do not themselves establish that every two-junk circuit has a cover satisfying the bound.

## New concrete geometry result

`inventory_residual_overlap.lean`, namespace `...MutualBudget`, final `residual_overlap_excludes_other_raw`:

- Assume a bipartition, NoFourCycle, leastness, TopForm, `junk = {g,h}`.
- Suppose `r` belongs to both raw sides of `g` and `t` belongs to `wmax(g)` and raw side 0 of `g`.
- If `Ustar \ coveredByJunk` is nonempty, then `r` belongs to neither raw side of `h`.

No purity, junk order, independence, singleton-intersection, or wide-arm assumption is needed. Proof: a residual oriented pair a,q makes r a cleaner of h. If r occurs in an h arm, the other arm forces r adjacent a or q. The first yields a four-cycle with t,q; the second yields a triangle with t, ruled out by the bipartition. Residual exclusive arms and free-of-wmax supply all distinctness conditions. The preceding helper `wmax_raw_opposite_adj` obtains adjacency from a cleaner in one raw arm and any input in the other arm.

This file is frozen, 1855 lines, SHA256 `beea6e5932e4a58b5dd63ee4192d3e796e999611d700cac46d557b59b8cdec57`. Direct recheck exited 0, full logs `inventory-residual-overlap-recheck.stdout` and `.stderr` in the job scratch directory. Only the inherited unused-section-variable warning occurs. Structural and antecedent agents independently cleared it.

## Closest concrete guarded-only subcase

For the earliest junk with singleton overlap {r}, internal cleaner t, and pure raw arms P,Q oriented so r is in P and Q and t in P, the guarded accepted graph is the union of r-W and t-Q. The following composition appears close but is **not yet formalized as one theorem**:

- Require every Ustar edge to lie in those two stars. Assign edge r-t to the r-star, so selected t-star leaves Y exclude r.
- Partition r-star leaves by actual tracing: non-h-accepted leaves with a nonempty mixed reading side give the fixed-g mixing antichain A; the remaining leaves come from centreless-top opposite raw sides or from h acceptance.
- Select one actual raw root per relevant centreless top, plus one actual h operand missing r (the structural `singleton_joint_other_missing_side` helper). Bound root count by `centreless.card + 1` and verify selected star leaves are covered.
- Toolchain's checked `forest_neighbor_star_mixed_overhead` in `guarded_neighbor_anchor_budget.lean` uses the ordinary neighbor anchor r in Q and the opposite-color mixed P root to pay the extra h root: selected forest leaves plus Y are bounded by `splitExtra.card + centreless.card`.
- Combine with |A| charged leaves and two active centers, then apply `guarded_antichain_cover_exclusion`.

The remaining formal step in this subcase is the **actual finite edge assignment and root selection/cardinality proof**, including mixed/centreless/h-accepted cases and all empty-set cases. No claim is made that arbitrary remaining Ustar edges satisfy the guarded-only hypothesis.

## Global unresolved cases

The full target still needs a disjoint accounting or replacement argument combining guarded contributions of both junk gates with mutual residual edges. Adding independently obtained covers and OR budgets is invalid because their charged OR sets can overlap. Current strict overlap and color-separated budgets provide tools, not a completed case split. Nested junk requires the separate restriction/flag route; first-rung rewrites need actual earlier wires and preservation of all Ustar edge inputs.

Do not assume any of these false shortcuts:
- Every nonflag junk has all accepted Ustar edges in one available clean star: P4/P5 geometry-only examples disprove this form. The P4 circuit is explicitly proved nonleast; P5 makes no leastness claim.
- In the singleton-overlap/Joint/residual case, all accepted edges fit r,t plus one additional center: the C6 example in antecedent search disproves it.
- Even a flexible three-center cover of the accepted union is not generally available: antecedent search found a theta(3,3,3) example with a matching of size four. The fourth matching edge is h-only and unguarded, so it cannot be an actual Ustar edge under the guarded-or-joint decomposition. Corrected finite scans of admissible guarded-or-common edges found no matching of size four. No general admissible-edge theorem or target refutation follows.

## Frozen-source hygiene

`inventory_colored_budget.lean` is an untracked working duplicate, byte-for-byte identical to frozen `inventory_residual_complete.lean` (1775 lines, SHA256 `301f39408fdce739c2ac5fdbfcbc3a305a7c95b01d06c2117d6a4ca66f366ba8`). It contains no unique result and does not need separate preservation.

The latest inventory source family has no sorry, new axioms, native_decide, forbidden namespace escape text, string literals, attributes, or set_option commands. Imports are Defs/Mathlib only. Final PR integration still must respect the single-file size and single-theorem rules; copied helper declarations may need theorem-to-lemma normalization by root.
