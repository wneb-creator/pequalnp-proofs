# L-meta-971: lean_setup checkpoint

Checked Heawood graph fixtures, complete monotonicity-critical rows, and a 27-gate upper bound; not the posted lower bound.

Each listed source previously completed with exit code 0 using the repository's pinned Lean 4.36.0 toolchain and Mathlib cache. The saved compiler logs are complete stdout/stderr; these successful runs emitted no output. `validation.json` records exact source hashes, imports, log paths, and observed statuses. No target file has been accepted by the posted-statement checker.

| Source | Complete compiler log | Exit | Checked scope |
| --- | --- | --- | --- |
| `HeawoodFixture.lean` | `compiler/HeawoodFixture.log` | 0 | Graph invariants, seven-edge matching, cover lower bound seven, exact 37-independent-set cover, and equivalence between 58 critical rows and full monotone correctness. |
| `HeawoodUpper.lean` | `compiler/HeawoodUpper.log` | 0 | Exact 27-gate Monotone2 circuit for the posted 21-edge function on all Boolean inputs. |
| `CriticalRows.lean` | `compiler/CriticalRows.log` | 0 | General critical-row theorem from a family covering every independent set. |

## Reproduction and dependencies

From the repository's `lean/` directory, run `lake env lean ../results/pequalnp-pilot-4b/L-meta-971/lean_setup/<Source>.lean` with the pinned toolchain and the prepared Mathlib cache. Never update the dependency pins. All scratch definitions needed by these sources are included in each file; there are no imports of another scratch file. Files sharing helper prefixes are standalone checks and should not be concatenated.

Mathlib and `PEqualNP.Defs` are existing project dependencies. Some L-lib-123 runtime helpers additionally import the existing tracked modules `PEqualNP.Library.Evasion.MBudget`, `PEqualNP.Library.Evasion.MTrans`, `PEqualNP.Library.Machines.IterMeasure`, or `PEqualNP.MetaComplexity.Helpers.Machines.Zip`. Their sources and transitive dependencies are already preserved in this repository; build those project modules with the pinned cache before checking the relevant standalone file. The exact direct imports are recorded in `validation.json`.

## Limits

The 26-gate searches yielded no proof or counterexample. Actual-circuit normalization, a circuit-to-CNF theorem, and a checked UNSAT certificate remain absent. The exact 58-row semantic bridge itself is proved.

## Independent checks

The 27-gate construction was independently evaluated on all 16,384 inputs; the graph cover was independently enumerated. The CNF encoder was separately reviewed, without treating solver output as a proof.

This checkpoint contains checked sources, successful compiler output, and scope metadata only. It contains no solver trace, failed compilation probe, or proof-gap placeholder. It was preserved under the parent's explicit push-early instruction. lean_setup did not stage, commit, or push these files.
