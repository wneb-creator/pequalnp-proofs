# Shared lemma inventory

Read this index together with `../NOTES.md` before starting a new assignment.

The integrated source of truth is `lean/PEqualNP/Outside/L_meta_1024.lean` from the repository root (the relative link from this folder is `../../../lean/PEqualNP/Outside/L_meta_1024.lean`). Its original 4,455-line checkpoint builds; the current 4,041-line source also compiled after the reviewed removal of unused demonstrations. It does not yet contain the exact named theorem.

- `Sink.lean`: immutable independently reviewed standalone development, including its existing dependencies. Full build log: `../validation/sink-build-001.log`. New namespaces/lemmas are Sink.clamp, gate, transform, transform_sink, band_correct, preserves_ordinary, and exotic_subset.
- `four_or_sinks.md`: mathematical high-gate argument, requiring formalization.
- `four_sink_review.md`: independent review and normalization bridge, requiring formalization.
- `four_exotic_reduction.md`: mathematical paid-source reduction, requiring formalization.

Main-file namespaces include Global, Support, Clamp, Clamp9, Charges, Bridge, Cut, OneAnd, and OneAndCircuit under `PEqualNP.Outside.L_meta_1024_aux`. Parent namespaces already define line/row/val names: qualify Global.line, Global.val, Support.line, and Support.row explicitly to avoid accidental shadowing.

Put new stable, compiled components here only after review. Work in an individually owned scratch file first. Record assumptions and exact scope in the shared notes; a conditional theorem is not the posted theorem. Do not add sorry, new axioms, native_decide, bv_decide, forbidden options/attributes, strings, or the forbidden root-namespace token to a candidate proof file.

- `ThreeTriples.lean`: compiled standalone component-counting lemma for three essential triples; independently reviewed and approved. Full log: `../validation/three-triples-build-001.log`.

- `SharedParent.lean`: compiled semantic dependence lemma for shared high parents; independently reviewed and approved. Full log: `../validation/shared-parent-build-001.log`.

- `DeadCore.lean`: compiled paid-cut bridge and dead-gate compiler structure/count/index lemmas; evaluation preservation is still being developed separately. Independently reviewed and approved. Full log: `../validation/dead-core-build-002.log`.

- `Ownership.lean`: compiled and independently reviewed finite high-parent ownership selector. Full log: `../validation/ownership-build-003.log`.
- `HighNetwork.lean`: compiled and independently reviewed conditional six-gate bound for the common low prefix of four OR outputs; not the full circuit theorem. Full log: `../validation/high-network-build-002.log`.

- `Dead.lean`: compiled and independently reviewed semantic preservation and operation-tag preservation for dead-gate deletion under NoReads. Full log: `../validation/dead-build-002.log`.
- `Compiler.lean`: compiled and independently reviewed deleted-root formula and paid-cut compiler wrappers. Full log: `../validation/compiler-build-002.log`.

- `FourPairs.lean`: compiled reduced four-output impossibility theorem using band correctness alone; independently reviewed and approved. Full log: `../validation/four-pairs-build-003.log`.

- `AppendLine.lean`: compiled three-OR-gate constructor with exact output semantics and preservation of earlier wires; independently reviewed and approved. Full log: `../validation/append-line-build-002.log`.

- `Reduction.lean`: compiled and independently reviewed sink-cut invariance and paid-source clamping correctness under the explicit twelve-source/four-raw-input hypotheses. Full log: `../validation/reduction-build-001.log`.

- `FirstAnd.lean`: compiled and independently reviewed first-AND surgery and OR-sink normalization preserving any specified ordinary-output family, without increasing gate count. Full log: `../validation/first-and-build-002.log`.
- `PairSurcharge.lean`: compiled and independently reviewed four-charge lower bound from two overlapping pair cores in an ordinary four-point output. Full log: `../validation/pair-surcharge-build-001.log`.

- `Assembly.lean`: compiled and independently reviewed append-list and deleted-OR-root interfaces. Full log: `../validation/assembly-build-002.log`.
- `SmallFamily.lean`: compiled and independently reviewed nonordinariness of all four outputs in a hypothetical eleven-gate residual. Full log: `../validation/small-family-build-001.log`.

- `FourBound.lean`: checked and reviewed 39-gate bound for nine ordinary outputs and four OR sinks.
- `NineOrdinary.lean`: checked and reviewed removal of those root/sink hypotheses; any counterexample below39 gates has at least five globally nonordinary outputs.
- `MissingRawWitness.lean`: checked and reviewed fixed-set witness lemma supplying at most two raw sources and nine distinct paid pair-core witnesses when a required raw point is missing.

- `AbnormalAnd.lean`: checked/reviewed positive-certificate bound and eight-AND necessity for an abnormal output.
- `ExcessSupport.lean`: checked/reviewed thirteen-input support and twelve-gate-cone necessity for an abnormal output.
- `Clamp11.lean`: checked/reviewed fixed-paid-family raw-source inclusion for the five-exception budget.
- `ResidualFamily.lean`: checked/reviewed append-complement induction helper and five-output nonordinariness.
- `FiveReduction.lean`: checked/reviewed conditional reduction to five nonordinary, globally bounded OR pairs over at most nine internal gates. Its remaining paid/raw hypotheses are explicit.

- `FiveOwned.lean`: checked/reviewed eight-ordinary reduction discharging all paid/raw/root/sink assumptions; returns five nonordinary globally bounded OR pairs over at most nine internal gates. This is a reduction, not the five-output impossibility. Full log: `../validation/five-owned-build-002.log`.

- `ParentRankGeometry.lean`: checked/reviewed five-line union cardinality at least11 and impossibility of five distinct lines through one point; exact finite Singer geometry, not a circuit bound. Full log: `../validation/parent-rank-geometry-build-001.log`.

- `ConnectedCore.lean`: checked/reviewed rank at least10 for connected minimum-degree-two parent graphs and five-edge stars, plus common labels for nonleaf vertices. General connected graphs with leaves and circuit application remain open. Full log: `../validation/connected-core-build-002.log`.

- `FalsePruning.lean`: checked/reviewed 39-gate bound when every output has capped minimum formal false-certificate cost at most4; any smaller correct circuit has an output with formal cost at least5. Additive cost counts repeated occurrences; no assumption follows from semantic support alone. Full log: `../validation/false-pruning-build-003.log`.

- `ConnectedLeaves.lean`: checked/reviewed connected rank bound with at least two core edges.
- `ConnectedDouble.lean`: checked/reviewed double-star case and full connected parent-graph rank theorem, allowing arbitrary parent indices, loops and repeated pairs. Actual circuit application remains separate. Full logs are the corresponding `connected-*-build-*.log` files in `../validation/`.

- `Ancestry.lean`: checked/reviewed prefix-valid syntactic ancestry and component-label invariant.
- `TwoPairs.lean`: checked/reviewed impossibility of two distinct nonordinary OR outputs over at most six internals, and at least four of five outputs using one of the last three internals. Full logs: `../validation/ancestry-build-002.log` and `../validation/two-pairs-build-002.log`.

- `ConnectedCircuit.lean`: checked/reviewed direct application of connected parent rank to arbitrary circuit indices; under the eight-ordinary reduction the actual five-pair parent graph is disconnected. No simple-graph or first-occurrence hypothesis is added. Full log and durable status: `../validation/connected-circuit-build-002.log` and `.exit`.

- `Collective.lean`: checked/reviewed directed path inside the original fixed selected cone while avoiding every node of another selected cone, using exact prefix-valid edges. The global graph-count inequality remains open. Full log/status: `../validation/collective-build-002.log` and `.exit`.
