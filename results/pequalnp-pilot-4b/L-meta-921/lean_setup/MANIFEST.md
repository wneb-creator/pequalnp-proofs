# L-meta-921: lean_setup checkpoint

Checked cyclic-plane incidence and monotone critical-input lemmas; not the posted 39-gate lower bound.

Each listed source previously completed with exit code 0 using the repository's pinned Lean 4.36.0 toolchain and Mathlib cache. The saved compiler logs are complete stdout/stderr; these successful runs emitted no output. `validation.json` records exact source hashes, imports, log paths, and observed statuses. No target file has been accepted by the posted-statement checker.

| Source | Complete compiler log | Exit | Checked scope |
| --- | --- | --- | --- |
| `CyclicPlane.lean` | `compiler/CyclicPlane.log` | 0 | All 13 cyclic lines have size four, distinct intersections have size one, point degrees are four, and related complement/union cardinalities. |
| `DenseCritical.lean` | `compiler/DenseCritical.log` | 0 | For a monotone predicate, correctness on the weight-eight layer and the maximal outside-line input implies correctness throughout the dense promise. |

## Reproduction and dependencies

From the repository's `lean/` directory, run `lake env lean ../results/pequalnp-pilot-4b/L-meta-921/lean_setup/<Source>.lean` with the pinned toolchain and the prepared Mathlib cache. Never update the dependency pins. All scratch definitions needed by these sources are included in each file; there are no imports of another scratch file. Files sharing helper prefixes are standalone checks and should not be concatenated.

Mathlib and `PEqualNP.Defs` are existing project dependencies. Some L-lib-123 runtime helpers additionally import the existing tracked modules `PEqualNP.Library.Evasion.MBudget`, `PEqualNP.Library.Evasion.MTrans`, `PEqualNP.Library.Machines.IterMeasure`, or `PEqualNP.MetaComplexity.Helpers.Machines.Zip`. Their sources and transitive dependencies are already preserved in this repository; build those project modules with the pinned cache before checking the relevant standalone file. The exact direct imports are recorded in `validation.json`.

## Limits

No complete lower-bound proof or validated 38-gate counterexample. The large unsuccessful PairAutomorphisms probe, solver instances, traces, and unvalidated candidates are deliberately excluded.

## Independent checks

The separate source encoder received an independent semantic review, but no Lean circuit-to-CNF or UNSAT bridge was completed.

This checkpoint contains checked sources, successful compiler output, and scope metadata only. It contains no solver trace, failed compilation probe, or proof-gap placeholder. It was preserved under the parent's explicit push-early instruction. lean_setup did not stage, commit, or push these files.
