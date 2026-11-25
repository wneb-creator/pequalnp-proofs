# L-meta-1772: checked partial results

Status: the posted theorem is not proved or refuted. No proof PR has been opened and the full-statement checker has not been run. All Lean files here are research components; they are not submissions of the posted statement.

## Most useful files

| File in `lemmas/` | Checked result | Remaining assumption or limitation |
| --- | --- | --- |
| `forest_route.lean` | Full target conclusion for every acyclic graph, including empty and disconnected graphs | Does not cover cyclic graphs |
| `canonical_bad_route.lean` | A minimum circuit chosen with least junk, TopForm, then least bad-AND count in the stated comparator class | Does not prove bad count is zero |
| `single_edge_signature_route.lean` | A bad AND in the nested canonical class must be true on a second distinct unordered graph edge | Second truth witness need not be pivotal |
| `prefix_patch_route.lean` | Simultaneous replacement of selected gates by a safe prefix, with arbitrary fanout and strict junk decrease | Requires size budget and relations on all graph-positive pairs and graph-negative inputs |
| `protected_product_patch_route.lean` | Two conditional aliases plus a protected safe product give a no-larger strict-junk repair | Requires the two aliases and protected-product hypotheses |
| `rectangle_exchange_route.lean` | Complete opposite-rectangle cluster repair | Requires three AND signatures and available OR sources |
| `shared_side_exchange_route.lean` | Complete shared-side cluster repair, seven cases | Requires three AND signatures and two available OR sources |
| `shared_hybrid_topform_route.lean` | Excludes a common-product hybrid pattern from canonical minima | Requires the stated global semantic signatures |
| `augmented_exchange_route.lean` | Two 19-gate circuits compute one 12-vertex, 14-edge graph; one has a bad gate, the repaired one has every AND owning an edge | Minimum size 19 is UNVERIFIED; this is neither a target proof nor a refutation |

These files are standalone snapshots. Several copy earlier infrastructure into the same auxiliary namespace. Do not import or concatenate every file together: use the appropriate superset, or extract only its new suffix during final assembly.

## Open implication

An arbitrary first bad AND in the chosen minimum circuit has not been shown to expose any of the repairable clusters. Its input signals may involve large OR supports or earlier AND outputs. Shared readers can prevent a local simplification from meeting the gate budget. Neither the girth assumptions nor the current ownership and pivotality lemmas have closed that implication.

The available reduction quota for this gap was already full (three live reductions) at assignment. No fourth reduction was submitted.

## Validation and provenance

`statement.txt` is the exact posted statement. `assignment.json` contains public gap metadata without the lease. `validation.txt` retains full successful Lean output and explicit scope limitations. `NOTES.md`, `TIMELINE.md`, and `SOURCE_MINING.md` describe strategies, source adaptations, and independent reviews. Finite-search scripts, complete logs, and review manifests are in `finite/`.

Finite BFS/SAT results are computational evidence, not Lean proofs. UNKNOWN/timeouts are recorded as such. The augmented benchmark uses pure Boolean rewriting and case splitting; an unpushed earlier native-evaluation draft was rejected during review. The audited final declarations depend only on propext, Classical.choice, and Quot.sound.

## Reproduce a component

Use Lean 4.36.0 and the repository Mathlib revision with its binary cache. From `lean/`, run `lake env lean ../results/orch/lemmas/forest_route.lean` (or another selected standalone file). No `lake update` is needed. The task container used a scratch Lean installation, so its absolute scratch paths are not portable.

All partial commits were independently reviewed before pushing to the fork branch `pnp/pilot-77`. A final proof PR would need a clean diff adding only `lean/PEqualNP/Outside/L_meta_1772.lean`, with exactly the posted theorem, followed by the named build and repository checker.
