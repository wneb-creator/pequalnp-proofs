# L-meta-1772: preserved partial work

Job: pequalnp-pilot-66. Message: msg-9ba21292ed59c7175c6f44f3.

The posted ownership theorem has not been proved or refuted. There is no proof PR and no repository-checker ACCEPTED verdict. This branch preserves partial Lean results and reproducible diagnostics; it is not a valid single-file proof PR as it stands.

The exact assigned statement is in `statement.txt`. The permitted project import is `PEqualNP.Defs`. The work started from upstream commit `ea08af8ef39f0debe53b9976731aed295685ab32`, with Lean 4.36.0 and pinned Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

## Most useful checked components

- `lemmas/IntegratedNormalForm.lean`: for every finite graph with a nonempty edge set, a public minimum circuit can simultaneously be TopForm, minimize dirty-AND count then AND-ancestor pairs then unowned-AND count, and have at least two distinct pivotal edges at every dirty or unowned AND. No girth assumption is needed for this partial theorem.
- `lemmas/JointNormalForm.lean`: every finite graph has a minimum monotone circuit with least dirty-AND count, then least unowned-AND count. Every dirty or unowned AND in that circuit has at least two distinct unordered pivotal edges.
- `lemmas/JointPivotalReplacement.lean`: a Monotone2 replacement with a valid output wire, whose AND gates and output reject every graph-negative input and whose output covers the edges jointly lost by disabling a finite gate class, can replace that class. It preserves the graph function and does not increase size when its cost fits the deleted class. It strictly reduces dirty-AND count if the class contained a dirty AND.
- `lemmas/MinimalAO2.lean`: every minimum circuit in the public monotone model already has exactly two earlier inputs per gate. This changes neither the circuit nor its measures.
- `lemmas/PivotalPairMeasure.lean`: the singleton-pivotal repair also does not increase the AND-ancestor-pair count, allowing a compatible lexicographic normalization.
- `lemmas/DoubleStarRepair.lean`, `lemmas/SharedFactoryRestriction.lean`, and `lemmas/FactoryBoundaryBudget.lean`: concrete shared-filter repairs and geometric/counting lemmas under explicit structural hypotheses.

Every file listed above compiled separately with the pinned Lean toolchain and passed independent source/format review. Complete build logs and reviewed source hashes are recorded in `validation.txt`. For example, from `lean/`:

```sh
lake env lean ../results/orch/lemmas/JointNormalForm.lean
lake env lean ../results/orch/lemmas/JointPivotalReplacement.lean
```

These are partial helper files, not proofs of the exact posted statement. The named final file has not been submitted to `tools/check-lean.mjs`.

## Unresolved argument

The current route needs a replacement within the gate budget when a suitably normalized minimum circuit still contains an unowned AND. The replacement must handle arbitrary sharing and dirty AND readers, not only literal-centered sound filters. Existence of a suitable jointly pivotal gate class and covering circuit remains unproved.

The clean-class criterion is needed only for a selected minimum that still has an unowned AND. Already-owned dirty ANDs are permitted by the posted goal. Neither the conditional replacement theorem nor the finite repair examples establish the missing general criterion.

## Diagnostics and limits

`search/`, `search2/`, and `search3/` preserve solver encodings, complete logs, witnesses, validation, and manifests. Restricted-model UNSAT results are not Lean lower bounds. Long stress-graph and Petersen searches have not produced a counterexample; timeouts and interrupted runs are UNKNOWN.

`heuristic/` preserves a completed Petersen rewiring run and an interrupted stress-graph run. Their saved best circuits are incorrect and are explicitly labeled as such. `attempts/` contains an interrupted finite Lean attempt, clearly excluded from the compiled-source census.

No full-proof cleanup pass has been performed because the exact theorem is unresolved. See `NOTES.md` for the mathematical frontier and `TIMELINE.md` for timestamps. The validation record contains the required sub-agent and elapsed-time measurements.
