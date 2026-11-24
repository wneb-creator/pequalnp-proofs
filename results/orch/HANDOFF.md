# L-meta-1477 proof handoff — proof status as of 2026-11-24 11:48 UTC

The posted claim remains unproved and unrefuted. It excludes every monotone fan-in-two circuit of at most124 gates computing the exact42-input,105-edge projective-plane incidence function. The checked standard construction uses125 gates. No target-sized correct counterexample was found. Every result below is a restricted lower bound, auxiliary theorem, or conditional counterexample lift; none is the final posted theorem.

## Strongest checked lower bounds

|Scope|Checked API / frozen file|Restrictions that remain|
|---|---|---|
|Zero or one dirty AND after least-AO/TopForm normalization|`PlaneOneJunkFull.lean`; named partial `lean/PEqualNP/Outside/L_meta_1477.lean`|The named partial derives at least two dirty gates from an arbitrary posted short circuit. It does not prove the gap.|
|Exactly two dirty gates, a residual edge outside every input-mask family|`PlaneTwoJunkPrivate.private_pair_size_of_card`, `PlaneTwoJunkPrivate.lean`|LeastAO, TopForm, exact two junk gates, both raw operand-side pairs disjoint. The private edge derives needed independence and product/reader facts. Contrapositive `short_two_junk_all_masked` covers all residual pairs by actual masks.|
|Exactly two first-layer products, two effective internal clean centers each|`TwoProductAllReaders.two_product_lower_bound_of_centers`, `TwoProductCenters.lean`; concrete `plane_size_of_centers`, `PlaneTwoProductCenters.lean`|Every dirty operand has no AND ancestor along OR paths; all four raw supports have cardinal at least2. Two clean centers each. Disjointness is derived. No no-joint, all-masked, minimum-junk, or reader-path premise.|
|Exactly two first-layer products, one clean-center set empty|`ZeroProductCoverage.plane_zero_product_size`, `PlaneZeroAllSizes.lean`|Exact two dirty gates with pure OR operands and both operand-side pairs disjoint. No support-size, no-joint, all-masked, private-edge or reader premise remains.|
|Singleton side0 plus one nontrivial product|`SingletonIntegration.singleton_other_lower_bound`, `SingletonOtherLowerBound.lean`; `PlaneSingletonMinimum.lean`|Exact two first-layer/disjoint products, singleton at side0, other supports at least2, no productive joint. Other two-center condition is explicit or follows from globally minimum junk in the plane wrapper.|
|Both side0 singleton products, all pivot colors and all reader counts|`SingletonSameColorIntegration.both_singleton_lower_bound_of_pure` and `plane_both_singleton_pure_size`, `PlaneSingletonPairPure.lean`|Exactly two first-layer dirty gates, each with actual side0 singleton. Disjointness is derived; no no-joint, minimum-junk, center-count or pivot-color premise remains.|
|Many first-layer products with sufficiently many centreless readers|`ManyProductLowerBound.lean`|Disjoint supports of size at least2, two centers per product, no productive joint, and explicit `3*t <= 2*centreless.card + junk.card`.|

Here first-layer means the precise no-AND-along-OR-path premise in the files. A dirty gate is an AND whose full Boolean function is not below the target graph function. Clean-center counts are static product-mask sets, not the number of arbitrary circuit readers. All singleton results currently fix the singleton operand at side0; no general input-swap transport has been supplied.

## Normalization and overlap restrictions

`MinimumJunk.lean` chooses a least-size AO circuit with globally minimum junk count, then uses exact-junk-preserving TopForm normalization. `FirstLayerMinimum.lean` excludes a sole effective internal side mask under first-layer/no-productive-joint assumptions. `FirstLayerTwoCenters.minimum_junk_two_effective_centers` additionally requires TopForm and disjoint operand supports to derive at least two effective masks. `FirstLayerEffective.lean` excludes no effective masks under its explicit TopForm, first-layer/no-productive-joint and leastness premises.

`DoubleOverlapElimination.minimum_junk_no_double_overlap` in `DoubleOverlapElimination.lean` rules out an exact two-element operand overlap under leastAO/TopForm, C4-freeness, global minimum junk, first-layer and no-productive-joint assumptions. `FirstLayerOverlap.singleton_overlap_two_kinds` classifies an exact singleton overlap under leastAO/TopForm, global minimum junk, C4-freeness and bipartiteness, pure operands for all dirty gates, no productive joint involving the target gate, and both target supports of cardinal at least2. Under those premises it forces one internal and an external effective mask; it does not eliminate that case. Larger overlaps and genuinely dependent dirty gates remain open. Shared mixed OR cones prevent simply reusing the private one-junk rotation argument.

`PairShadowElimination.minimum_junk_no_covered_pairs` in `PairShadowElimination.lean` is stronger than the earlier first-layer sensitive-mask adapter: in a globally minimum-junk leastAO representative, a dirty gate with an internal clean mask cannot have every accepted positive host pair contain that mask vertex. It needs no first-layer, TopForm, no-joint or C4 premise. The unique-center connector application is ongoing; this adapter alone does not close the remaining1/1 or1/2 profiles.

## Open parts of the posted statement

- Arbitrary numbers of dirty gates, especially three or more, have no complete reduction to the checked two-gate cases.
- Dependent dirty AND gates and general overlapping operand supports have no universal normalization.
- Large first-layer two-product profiles1/1 and1/2 remain outside the completed2/2 and zero-center branches.
- Mixed singleton/nontrivial shapes retain their explicit no-productive-joint or minimum-junk conditions; the complete both-side0-singleton branch is now checked. Preserve exact premise lists rather than treating computational examples or conditional counting budgets as universal lemmas.
- The multi-filter route still assumes at most one active cleaner per live mask OR gate. `MultiFilterBudget.multiple_filter_ordinary_budget` and `SharedFilterEdgeCover.active_edge_cover_bound_with_roots` supply counting pieces, but the actual separate-component construction and ordinary-owned-boundary treatment are incomplete. See `lemmas/SharedFilterRoute.md`.

## Counterexample route and artifacts

See `SEARCH_HANDOFF.md` for exact search scopes, logs and INVALID artifacts. Checked local baseline/target/lift costs are: Hyperoval35/34/+90, Alternative6 29/28/+96, Triangle9 53/52/+72, Complement12 71/70/+54. Complete lifts are conditional on a genuinely correct target-size local circuit. Finite-basis and DNF-table certificates are ready for a concrete witness, but none has been found. Restricted SAT UNSATs and search timeouts do not prove the gap.

## Rebuilding and preservation

Portable rebuild: follow the repository CONTRIBUTING instructions and build queue, install the Lean version pinned by `lean/lean-toolchain` (`leanprover/lean4:v4.36.0` in this snapshot), and obtain the matching Mathlib cache with `lake exe cache get` before the first build. From the repository `lean/` directory, run `lake env lean ../results/orch/lemmas/FILE.lean`, redirecting complete stdout/stderr to a log. In this container only, source `/tmp/oec/pequalnp-pilot-29/lean-env.sh` first to select the prepared toolchain; that temporary script will not survive container loss and is not required in a correctly configured portable environment. The named partial is built with `lake build PEqualNP.Outside.L_meta_1477`. Never run `lake update` or rebuild Mathlib from source. The pinned environment and warm cache were prepared earlier.

Large combined results are intentionally preserved under `results/orch/lemmas/`; several exceed the512KiB proof-file cap. Examples: `PlaneTwoProductCenters.lean`664978bytes, `PlaneTwoJunkPrivate.lean`666647bytes, `PlaneSingletonMinimum.lean`606272bytes, and `PlaneSingletonPairPure.lean`692104bytes. They are reusable checked components, not compliant final one-file submissions. The named module remains a smaller partial and the local checker correctly rejects its missing exact final theorem.

`lemmas/AssemblePrivateBranches.py` deduplicates exact normalized declarations and records full source/declaration hashes. Its known limitation is an indented top-level ` def OrdinaryActive`: remove only exact duplicate blocks, record the post-assembly cleanup, and rebuild. Older assembly manifests may hash the assembled prefix before a final wrapper was appended; use explicit final-file hashes/review logs where recorded. Frozen snapshots are immutable. Author build logs and independent reviews are preserved in the push validation packages.

Root alone owns the desk lease and git delivery. No proof PR should be opened unless the exact posted theorem or an admissible Lean refutation passes the final build and checker. All new compiled components should be independently reviewed and pushed to `pnp/pilot-29` before releasing the lease.
