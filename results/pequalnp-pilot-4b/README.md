# Pilot 4b checked research checkpoints

These checkpoints preserve checked Lean partial results and complete validation logs under Ben's 2026-11-23 PUSH-EARLY instruction. **No complete proof or refutation of a posted gap was obtained.** The posted-statement checker was not run because no completed target proof exists. This branch is a research archive, not an eligible one-file proof PR.

| Gap | Checked results retained | Remaining obligation |
| --- | --- | --- |
| [L-lib-123](L-lib-123/) | Simulation budgets, replay and encoding helpers, conditional compression routes, and protocol counterexamples. | A uniform strict-exponent FP3 simulation. |
| [L-meta-952](L-meta-952/) | Frozen-NOT/cofactor lemmas, replacement criteria, and the 14-gate Fano upper construction. | The general one-NOT projective-plane lower bound. |
| [L-meta-921](L-meta-921/) | Cyclic-plane geometry, promise reductions, local circuit lemmas, and counterexamples to stronger auxiliary claims. | The complete dense-promise 39-gate lower bound. |
| [L-meta-971](L-meta-971/) | Exact 27-gate Heawood upper construction, graph invariants, the complete 58-row correctness criterion, and restricted counting lemmas. | The general 27-gate lower bound. |
| [L-meta-997](L-meta-997/) | The cases `y.card ≤ 2` and `1 ≤ y.card` with all disjoint output sizes at most `y.card + 1`; sparse-window, refund, freezing, and OR-only heavy-count lemmas. | The general two-window compensation argument. |

Counterexamples here refute proposed intermediate arguments only. They do not refute any posted statement. Solver UNKNOWN results and restricted UNSAT results are labelled separately and do not establish a target theorem. Large unfinished solver traces were not archived.

The archive contains 91 Lean source/check files and 15,226 Lean lines, including repeated helpers and diagnostics. Each gap contains its exact posted `statement.txt`. Contributor directories contain final Lean sources, complete compiler stdout/stderr, manifests or validation records, and scope notes. Empty compiler logs with recorded exit 0 are successful silent runs. Some Lean files are diagnostics or statement checks; duplicate helpers are retained with their original research context.

Use the repository's pinned Lean 4.36.0 toolchain and prebuilt Mathlib cache. With the source's listed project dependencies available, run `lake env lean /absolute/path/to/archived/File.lean` from `lean/`. Imports and any inlined dependencies are disclosed in each directory. Manifests identify original scratch locations for provenance; those scratch paths are not required to read the saved results.

[Validation and checker status](validation.txt), [independent review ledger](independent-review.md), and [artifact index](artifact-index.json) record the scope and verification evidence. All leases held by this job have been released. The desk returned no available next gap after both permitted retries. No PR was opened.

KIT-MESSAGE-ID: msg-9574e75c4a2464ba7a74e928
