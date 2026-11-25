# L-meta-2732 formalization findings

- The assigned statement is exactly the first hypothesis of `R_meta_582_773.lean`.
- `Circuit.eval` is a forward fold of gate evaluations; missing wire indices evaluate to false. `Monotone2` requires AND/OR operations and at most two inputs. No encoding loophole found.
- Three reductions for the assigned step already exist: `R_meta_2732_3`, `_427`, `_773`, matching the desk count of three live reductions.
- `L_meta_3537.lean` proves canonicality of all 65 first-two-gate representatives by describing every graph automorphism through 336 possibilities. It imports only `PEqualNP.Defs`.
- `L_meta_3539.lean` proves that the packed 58-row AND/OR evaluator correctly computes the Heawood target whenever it returns 2097151. Its proof can be copied into the permitted file if a circuit is found.
- The search agent has the packed rows and canonical prefix table from `R_meta_2732_3.lean`.
- The definitions root has 86 project modules and 67 direct Mathlib roots; exact roots are recorded in `/tmp/oec/pequalnp-pilot-70/formalization/defs-imports.json`.

Checked results:

- `PrefixNormalize.lean` compiled with exit 0 on its first attempt. It combines generic circuit renaming, minimum-score selection, and transport under automorphisms. Applying `canonical_prefix F raw (transport_prefix F)` gives the exact ordered, symmetry-minimal prefix shape required by the assigned statement from any raw prefix witness.
- `rename/Rename.lean` compiled with exit 0. Root has integrated and independently reviewed these helpers.
- `Baseline.lean` compiled with exit 0. It proves monotonicity, exact size 27, and exact Heawood edge-function semantics for the search agent's canonical star circuit. Full log: `baseline-check-4.log`. The broad propositional simplification takes roughly 87 seconds.
- `rename/BaselineExplicit.lean` also compiled with exit 0 and no warnings. It uses explicit disjunction cases and takes about 20 seconds of simplification, but is longer. Root may keep the original baseline. The optional Tauto/AC attempts were stopped or failed; they are not deliverables.
- `rename/PackedDecoder.lean` compiled with exit 0 and no diagnostics. Its 184 lines copy and adapt the checked decoder from `L_meta_3539`, importing only `PEqualNP.Defs`. `Packed.decode` turns the 58-row packed equality into correctness on every 14-input assignment.
- `PackedWitness.fragment` was checked in `AssemblyTest.lean` against the saved decoder olean, with exit 0 and no warnings (`assembly-check-2.log`). `PackedWitness.raw` takes two first gates, at most 24 tail codes, and one packed equality, and produces `prefixWitness`.

The complete future witness route is now checked component by component:

1. Prove the finite packed equality for a candidate program by kernel computation.
2. Apply `PackedWitness.raw` to construct the raw prefix witness.
3. Apply `canonical_prefix F raw (transport_prefix F)` to obtain the required symmetry condition.

The only missing substantive input is a circuit with at most 26 gates. The original 27-gate baseline is not a proof of the posted bound.

Prepared components:

- `BaselineTauto.lean` and `BaselineAC.lean` are abandoned experiments, not checked deliverables.
- `PrefixMin.lean`: choose a raw prefix witness of minimum numerical score, then derive canonicality from transport under automorphisms.
- `Transport.fragment`: transport raw prefix witnesses using input renaming and sorted fan-ins.
- Child agent `/root/formalization/rename_wires` prepared `rename/Rename.lean`: generic input renaming, suffix preservation, circuit size and monotonicity preservation.

All scratch Lean sources and complete build logs are under `/tmp/oec/pequalnp-pilot-70/formalization/`. No final-file edits have been performed by this strategy. Root owns integration and publication.

## Ambient-graph accounting extension

On resuming the lower-bound task, coordination with `lower_bound` identified a narrower missing lemma than global homogeneous-shadow extraction. The desired circuit has internal AND gates clean relative to a C4-free ambient graph G, while its output only accepts some target graph J on pair inputs.

`pair-clean/PairCleanSubgraph.lean` compiled on its first attempt with exit 0 and no warnings, after the lease renewal at 06:32:10 UTC. It adapts the first accounting section of `L_meta_1983.lean` into the assigned auxiliary namespace. `edge_finset_gate_bound` now counts J-edges while using G for owner uniqueness; `total_from_model` applies `cover_half` to J. The final checked theorem `pairCleanSubgraphBound` assumes only false output on all singleton inputs and true output on each J-edge pair. It concludes a J-cover T with `J.edgeFinset.card + T.card ≤ gs.length + 1`. No full truth-table equality, explicit J⊆G, or output-zero hypothesis is used. All internal low-weight AND cleanliness remains relative to G.

The source has 891 lines and only imports `PEqualNP.Defs`. Full output is `pair-clean/pair-clean-check.log`. Root and `lower_bound` were notified immediately for independent review and preservation. This supplies the requested accounting endpoint for a circuit obtained by removing a dirty gate; it is not an unrestricted Heawood lower bound.

## Zero-forcing and direct-consumer pruning

`prune/EraseWire.lean` compiled with exit 0 and no diagnostics (`erase-check-2.log`) and passed root's independent review. The wire map keeps references below the deleted gate, maps that gate to an alias, and shifts later references down one. The alias is either an earlier wire or a sentinel beyond the final wire array. Only suffix gates are remapped; leaving the prefix unchanged is essential for arbitrary invalid references. The checked fold invariant handles past, deleted, later, and invalid wires. `delete_zero` removes a slot containing the false gate `OR []`, preserving its function and reducing size by one. It does not identify a nonconstant original gate with zero.

`prune/EraseConsumers.lean` compiled with exit 0 and no diagnostics (`consumers-check-3.log`). It contains the unchanged checked erasure component plus `Consumers.fragment`. `alias_invalid` proves that an AND/OR gate with at most two inputs and an out-of-range false input is equivalent to an earlier wire or an always-invalid false sentinel. `delete_invalid_input` removes such a gate. `delete_zero_consumer` combines the two deletions: if a later gate directly consumes a chosen gate, the chosen-gate-forced-false circuit has a Monotone2 realization exactly two gates smaller. No reference-validity assumption is needed, and any later direct consumer works. Root and lower_bound were notified immediately; independent review is pending.

Independent review of lower_bound's `GoodOrEdgeBound.lean`: PASS. The reused `countUnion` and `dag_union_bound` declarations match `L_meta_1983` byte for byte. The strengthened OR count requires a common ambient neighbor, which is supplied at every charged OR by the existing local invariant. The triangle-free mixed-support exclusion is valid. This was reported to root before preservation.

Further checked pruning components: `ZeroMonotone.lean` (empty `zero-monotone-check-3.log`) proves pointwise gate and wire monotonicity, then that forcing a gate false cannot make any final wire newly true. `EraseClean.lean` (empty `erase-clean-check-2.log`) supplies the retained-gate index correspondence and transfers AND-false properties through safe alias deletion. `CleanPruning.lean` (empty `clean-pruning-check-3.log`) combines these into `prune_zero_consumer`: the two-gate-smaller forced-zero realization has every AND false on any input where all original ANDs except the chosen slot were false. These sources are stable for independent review; the composite ambient accounting endpoint is now checking.

Independent review of the child strategy's `rename/support-cost/SupportCounterexample.lean`: PASS. The six supports accept precisely a six-edge matching on pair inputs, which has no five-entry vertex cover. An explicit accepted independent triple shows why this only refutes the pair-only-safety auxiliary claim. All finite computations use kernel decision; no claim about unrestricted Heawood circuits is made.

## Exact one-dirty-gate accounting

`OneDirtyAccounting.lean` passed with exit 0 and empty `one-dirty-accounting-check-2.log`; sat_review independently approved the exact reused-source match and endpoint. `one_dirty_accounting` assumes a C4-free ambient graph G, singleton-false original output, all ANDs except one slot clean on low-weight G-false inputs, a later direct consumer of that slot, and J-edge acceptance by the forced-zero circuit. It produces a J-cover T with `J.edgeFinset.card + T.card + 1 ≤ original.size`. No full truth-table identification of J is assumed.

`OneDirtyLoss.lean` passed its first check with empty `one-dirty-loss-check-1.log` and independent sat_review approval. It combines the accounting endpoint with lower_bound's stable `RobustMatchingCounts.lean`, constructs J as the graph of positive forced-zero pair evaluations, and proves at least three of the 21 indexed Heawood edges are rejected after zero-forcing when original size is at most 26. This is an explicit necessary restriction, not an unrestricted 27-gate lower bound.

`UnusedSlot.lean` passed with empty `unused-slot-check-1.log`: forcing an unconsumed non-output gate false preserves the output. The suffix may use arbitrary operations and invalid references. `ZeroedAccounting.lean` passed with empty `zeroed-accounting-check-1.log`: one deletion gives the companion inequality `J.edgeFinset.card + T.card ≤ original.size` without any consumer hypothesis. A matching-based structural corollary that the only dirty non-output slot must have a consumer is now checking.

`DirtyConsumer.lean` passed its first check with empty `dirty-consumer-check-1.log` and sat_review approval. The no-consumer contradiction uses all 21 original indexed hits, `zero_unused`, one-deletion accounting, and the explicit seven-edge perfect matching. `LiveLoss.lean` then passed with empty `live-loss-check-2.log`. Its final `one_dirty_loses_three_without_liveness` assumes at most 26 gates, all 21 indexed pair hits, singleton-false output, a C4-free ambient graph, and cleanliness of all ANDs except one non-output slot. It concludes at least three of the indexed edges are lost when that slot is forced false. No consumer or liveness assumption remains. An actual dirty witness forces the non-output condition because its wire is true where the final target output is false. The final combined source is 1,903 lines, imports only `PEqualNP.Defs`, and has no forbidden forms.

## Shared frontier accounting for the clean prefix

At root's request, constructive and formalization developed an abstract frontier for old clean contributions at the first dirty AND. `frontier/Frontier.lean` passed with empty `frontier-check-1.log` and independent sat_review approval. Insertion ORs have nonempty singleton support and an empty-support child. Their selected empty children form a frontier whose cardinality is at most the insertion count. Strong induction sends every accepted pair outside both singleton endpoints of a positive-support root to a frontier hit. Each insertion copies its other child's support and is therefore excluded from the growing-OR edge charge.

The naive sum of insertion count and small-support OR count double-charged insertion ORs with singleton support. The corrected `frontier/SharedCover.lean` passed with empty `shared-cover-check-3.log`. It modifies `coverCert` at insertion ORs to copy the nonempty child; the omitted empty child is already a global frontier root. A strong-induction invariant says each accepted pair is covered by its local certificate or by the fixed global union of frontier certificates. The DAG paid set is small-support ORs minus insertion ORs, so the final bound is the cardinality of their union, counting each gate once. `positive_shared_cover` simultaneously covers accepted pairs outside support at every positive-support root. `reserved_not_growth` makes the disjointness from the GoodOrGrowth charges explicit. This is a clean-prefix accounting result; extending the certificate through the dirty gate and later consumers remains separate.

`frontier/FrontierBudget.lean` passed its first check with empty `frontier-budget-check-1.log`. `gate_budget` proves that the AND count, the growing-OR count (with any additional predicate, including common-neighbor ownership), and the cardinality of insertion ORs union small-support ORs sum to at most `N-k`. This makes the shared cover's charges disjoint from the edge-growth charges. `SharedCover.lean` independently passed constructive's review, recorded in `shared-cover-review.md`; sat_review is also reviewing. Sources have 82, 394, and 452 lines respectively and import only `PEqualNP.Defs`; forbidden-form scans are empty.

## Selected graph and accepting semantic trace

After the environment restart around 07:28 UTC, no checks were started until focused cache recovery was confirmed. The final `frontier/AcceptingPath.lean` is 391 lines, SHA256 `6df02f862703f9054691c3b9b36eb07a9a67248461996779f4cdb2ea8cfa06f1`, and passed with empty `accepting-path-check-3.log`; repo_review independently approved it. It contains the D=false clean-frontier extension, preferred clean-AND parent selection, the actual selected predecessor set, and the minimal-root accepting trace. CleanFrontier retains the strict bound on an escaping boundary index. The only helper instance was removed before this final check; selecting definitions use explicit local Decidable arguments. The AND acceptance assumption excludes the dirty slot, avoiding an implicit binary interpretation of an empty-input dirty AND.

`frontier/RootCover.lean` is 514 lines, SHA256 `d56457c7b36fac72b1117bfd4e20a5709516f36a6137abd201699da73fc65107`, and passed with empty `root-cover-check-3.log`. Its `root_cover_from_raw_filters` closes the semantic escape argument: a missing root pair follows an accepting selected path to the dirty node; minimality rules out earlier clean-boundary escapes, forcing the pair to meet both dirty operand supports and the large opposite support at a false-to-true flag transition. A supplied raw triple-filter cover then contradicts the missing dirty label. The raw-filter premise is localized to live D=false consumers selecting a D=true child, matching the J split. Explicit circuit-model, label, live-closure, and raw-filter-cover hypotheses remain. No circuit-size conclusion is asserted.

The remaining decisive size issue is the exceptional edge-birth budget: `GoodOrGrowth` assumes complete clean cross-supports and a small parent side, which can both fail at the dirty AND. The selected-cover and fork arguments do not themselves replace those hypotheses. A one-dirty bound would also leave circuits with multiple dirty gates. Root capped this line of work around 08:05 UTC; the final bounded assembly target is a coherent fork-cover cardinality endpoint using lower_bound's concrete labels constructor and checked live-DAG bound.

## Capped coherent fork-cover endpoint

At 07:55 UTC, before the 08:05 cap, `frontier/ForkCover.lean` passed its first combined check with exit 0 and an empty `fork-cover-check-1.log`. The stable source has 797 lines and SHA256 `c17d312e94ec6e139fe41709881f95afaea812ae8ece3e7f8aaf6b90be100c23`. It imports only `PEqualNP.Defs`; the forbidden-form and helper-instance scans are empty. Exact dependencies are the checked RootCover endpoint, lower_bound's checked SelectedLabels recursion, and checked LiveDagSupportBound, followed by the new `fork_cover_bound` assembly. The actual label function F is constructed, the root union T is constructed, and all former label-interface hypotheses are discharged. The theorem gives root-pair coverage together with `T.card ≤ R.card + B.card`.

Scope is still conditional: selected-graph branch, liveness, extra-arc, actual Boolean/support/flag semantics, and live raw-filter-cover hypotheses remain explicit. The live set and paid OR class must still be instantiated for the circuit model; the raw-filter cover must still be connected to the existing graph geometry. Most importantly, no exceptional dirty edge-birth accounting or multi-dirty exclusion was established. This endpoint must not be described as a 27-gate Heawood lower bound or as a refutation of the posted existential statement. No further one-dirty helper layers are being started after this coherent checkpoint.

## Exact witness generator and relaxed assembly smoke check

The self-contained bundle at `/tmp/oec/pequalnp-pilot-70/formalization/witness-generator/` now converts gate-triple JSON to the complete single-file proof format. `generate_witness.py` validates all 16,384 truth-table rows both before and after idempotent/duplicate/dead-gate simplification, checks the packed boundary output, then renders the inline decoder, raw witness, input renaming, and canonical-prefix argument. Strict mode preserves the exact posted statement and rejects more than 26 normalized gates. It writes no output until all validations pass. Both the valid 27-gate baseline and an incorrect truncated26 circuit were rejected in strict mode with exit 2 and no output file.

The scratch-only `--relaxed-27-test` mode changes the four helper tail bounds and the one conclusion tail bound from 24 to 25; it cannot write into the repository and requires exactly 27 normalized gates. Its 541-line generated file `relaxed_27/L_meta_2732.lean` passed Lean with exit 0 after the 08:06:10 lease renewal. Full output is `relaxed27-lean-1.log` (16 existing deprecation/linter warnings, no errors). The file has only `PEqualNP.Defs` as an import, one outer auxiliary namespace, and the fully qualified final theorem. SHA256 is `87afdb03d65be33cdf5698ada77d82a02b3f6672aa4e2d23b729595c85871453`.

This smoke file proves only the weaker 27-gate statement and is not a proof of L-meta-2732. No 26-gate witness has been found yet, no relaxed file was copied into the assigned module, and no official checker result is claimed for the scratch file. Root received the strict generation/build command and all paths. Independent repo_review approval verified the exact posted statement, dependency hashes, format, smoke result, strict rejection logs, an additional relaxed-to-main negative test with no assigned-file change, and a 30-to-27 normalization regression. The manifest pins the exact posted statement and template. `validation.json` records the source hashes and complete test scope so preservation cannot confuse the smoke result with a completed gap.
