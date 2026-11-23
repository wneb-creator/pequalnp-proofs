# L-meta-952: lean_setup checkpoint

Checked finite Fano-plane upper-bound fixture; not the posted general lower bound.

Each listed source previously completed with exit code 0 using the repository's pinned Lean 4.36.0 toolchain and Mathlib cache. The saved compiler logs are complete stdout/stderr; these successful runs emitted no output. `validation.json` records exact source hashes, imports, log paths, and observed statuses. No target file has been accepted by the posted-statement checker.

| Source | Complete compiler log | Exit | Checked scope |
| --- | --- | --- | --- |
| `FanoUpper.lean` | `compiler/FanoUpper.log` | 0 | Fano incidence hypotheses and an exact 14-gate binary-OR circuit on every Boolean input, checked with ordinary decide. |

## Reproduction and dependencies

From the repository's `lean/` directory, run `lake env lean ../results/pequalnp-pilot-4b/L-meta-952/lean_setup/<Source>.lean` with the pinned toolchain and the prepared Mathlib cache. Never update the dependency pins. All scratch definitions needed by these sources are included in each file; there are no imports of another scratch file. Files sharing helper prefixes are standalone checks and should not be concatenated.

Mathlib and `PEqualNP.Defs` are existing project dependencies. Some L-lib-123 runtime helpers additionally import the existing tracked modules `PEqualNP.Library.Evasion.MBudget`, `PEqualNP.Library.Evasion.MTrans`, `PEqualNP.Library.Machines.IterMeasure`, or `PEqualNP.MetaComplexity.Helpers.Machines.Zip`. Their sources and transitive dependencies are already preserved in this repository; build those project modules with the pinned cache before checking the relevant standalone file. The exact direct imports are recorded in `validation.json`.

## Limits

No general lower-bound proof and no validated smaller circuit. Restricted solver UNSAT results and full-search timeouts are not Lean theorems and are not included in this checkpoint.

## Independent checks

The construction was independently evaluated on all 128 assignments before the Lean check.

This checkpoint contains checked sources, successful compiler output, and scope metadata only. It contains no solver trace, failed compilation probe, or proof-gap placeholder. It was preserved under the parent's explicit push-early instruction. lean_setup did not stage, commit, or push these files.
