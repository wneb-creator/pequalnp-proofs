# Selected graph and accepting paths: independent review

Reviewed by repo_review on 2026-11-25. PASS for the final stable sources as conditional helpers. No Lean job was started by this reviewer.

- `AcceptingPath.lean`: 391 lines, SHA256 `6df02f862703f9054691c3b9b36eb07a9a67248461996779f4cdb2ea8cfa06f1`; owner reports exit 0 and `accepting-path-check-3.log` is empty.
- `SelectedDirtyPaths.lean`: 164 lines, SHA256 `77ccf0da4bc6d6e05f2d81f822b2a812bec2c1b06b9044bb798c5072e2022190`; owner reports exit 0 and `selected-dirty-paths-lean.log` is empty.
- The `CleanFrontier`, `SelectedParent`, and `SelectedGraph` namespace blocks in the final combined source match the corresponding standalone sources exactly.

`CleanFrontier.pair_hit_boundary` explicitly assumes decreasing parent indices, acceptance behavior on inputs and ORs, clean ANDs having empty support, and the OR support/dirty-flag recurrences. An accepted pair outside a nonempty clean support descends through ORs until it reaches an erased empty-support clean child. The final conclusion correctly retains the strict bound `j < r`; recursion composes strict inequalities.

`SelectedParent` selects a small-support child whenever either child is small. If at least one parent is clean but the selected parent is dirty, the opposite parent is clean and has support larger than one. This depends on the explicit clean-parent premise. The initially declared global decidability instance was removed; the final definitions provide explicit local decidability arguments to their conditionals.

`SelectedGraph` keeps one child at an AND, removes the designated clean empty child at an insertion OR, keeps both children at other ORs, and has no children at the distinguished vertex or outside the gate range. Its theorems state their assumptions separately: parent order, unique distinguished dirty-AND behavior, OR dirty propagation, small-side support, and AND/OR acceptance recurrences. None of those properties is silently supplied by the definition.

`accepting_path_from_minimal_root` assumes input support is contained in its label, labels are monotone along selected arcs, all boundary vertices lie in the root set, and every root label lies in the proposed cover. It chooses the least accepting root. An erased accepted boundary would be a smaller accepting root, so every accepted descent outside the proposed cover follows selected arcs until the distinguished vertex. The proof does not assume the desired lower bound or a pre-existing accepting path.

`SelectedDirtyPaths` proves generic finite-path facts. The predicate-preserving descending-child premise yields a path to the distinguished vertex. Adding a selected child yields a consumer path; that helper itself does not require the starting consumer to be clean. The two-consumer fork theorem explicitly supplies clean, distinct starts, so neither start can occur inside the other's dirty suffix. The maximal-live-dirty argument uses clean roots, incoming-parent liveness and increasing parent indices; it does not need an unstated inclusion of the root set in the live set. The flag transition theorem yields some false-to-true transition, without asserting it is the last transition.

These sources do not establish an unrestricted circuit size lower bound or the posted 26-gate witness. Actual circuit instantiation must still prove their semantic, labeling and graph hypotheses. In particular, decreasing parent indices are not automatic for raw circuit references that may point forward or outside the available wires; a normalization or semantic treatment must justify that premise.

Final scans found no forbidden root escapes, strings, unsafe proof commands, added axioms, global instances or unsupported attributes. All imports are `PEqualNP.Defs`. Research packaging remains separate from the eventual single-file proof PR.
