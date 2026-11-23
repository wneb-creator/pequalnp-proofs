# L-meta-997: lean_setup checkpoint

Checked arithmetic aggregation and an actual-circuit diagnostic for the proposed two-window charging proof; not the posted inequality.

Each listed source previously completed with exit code 0 using the repository's pinned Lean 4.36.0 toolchain and Mathlib cache. The saved compiler logs are complete stdout/stderr; these successful runs emitted no output. `validation.json` records exact source hashes, imports, log paths, and observed statuses. No target file has been accepted by the posted-statement checker.

| Source | Complete compiler log | Exit | Checked scope |
| --- | --- | --- | --- |
| `Aggregation.lean` | `compiler/Aggregation.log` | 0 | Union/refund cardinal accounting, spare-gate compensation accounting, and target-weighted sum aggregation with all semantic charge assumptions explicit. |
| `PartialOverlap.lean` | `compiler/PartialOverlap.log` | 0 | Six-input, eight-gate one-NOT fixture satisfying the relevant hypotheses whose partial light/full heavy switched gate is absent from the exact refund. |

## Reproduction and dependencies

From the repository's `lean/` directory, run `lake env lean ../results/pequalnp-pilot-4b/L-meta-997/lean_setup/<Source>.lean` with the pinned toolchain and the prepared Mathlib cache. Never update the dependency pins. All scratch definitions needed by these sources are included in each file; there are no imports of another scratch file. Files sharing helper prefixes are standalone checks and should not be concatenated.

Mathlib and `PEqualNP.Defs` are existing project dependencies. Some L-lib-123 runtime helpers additionally import the existing tracked modules `PEqualNP.Library.Evasion.MBudget`, `PEqualNP.Library.Evasion.MTrans`, `PEqualNP.Library.Machines.IterMeasure`, or `PEqualNP.MetaComplexity.Helpers.Machines.Zip`. Their sources and transitive dependencies are already preserved in this repository; build those project modules with the pinned cache before checking the relevant standalone file. The exact direct imports are recorded in `validation.json`.

## Limits

Exact charge-intersection inclusion or full compensation remains unproved. The diagnostic refutes only a naive intermediate inclusion, not the target inequality. No target counterexample was found.

## Independent checks

fp3_strategy independently reviewed the original aggregation declarations; formal_audit independently reviewed the diagnostic fixture. Both confirmed the stated limited scopes.

This checkpoint contains checked sources, successful compiler output, and scope metadata only. It contains no solver trace, failed compilation probe, or proof-gap placeholder. It was preserved under the parent's explicit push-early instruction. lean_setup did not stage, commit, or push these files.
