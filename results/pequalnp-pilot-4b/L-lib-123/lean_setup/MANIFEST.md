# L-lib-123: lean_setup checkpoint

Prospective FP3 machinery. Baseline proves FP3 p p for p >= 1; no strict exponent saving is proved. The circuit-certificate and TM2 components remain conditional machinery, not a proof of the posted gap.

Each listed source previously completed with exit code 0 using the repository's pinned Lean 4.36.0 toolchain and Mathlib cache. The saved compiler logs are complete stdout/stderr; these successful runs emitted no output. `validation.json` records exact source hashes, imports, log paths, and observed statuses. No target file has been accepted by the posted-statement checker.

| Source | Complete compiler log | Exit | Checked scope |
| --- | --- | --- | --- |
| `Baseline.lean` | `compiler/Baseline.log` | 0 | Matching-exponent FP3 baseline using an actual linear input-length-clocked verifier. |
| `StackSummary.lean` | `compiler/StackSummary.log` | 0 | Exact prefix-replacement stack summaries, composition, and limitations of shortened summaries. |
| `CircuitCertificate.lean` | `compiler/CircuitCertificate.log` | 0 | Soundness and completeness of sorted source/reference records for BinaryCircuit evaluation, with an explicit permutation requirement. |
| `BlockReplay.lean` | `compiler/BlockReplay.log` | 0 | Independent replay equivalence when each event updates only its selected store entry; coupled equality does not factor this way. |
| `RadixPass.lean` | `compiler/RadixPass.log` | 0 | Actual TM2 stable radix pass, globally linear and non-lengthening. |
| `IterationBound.lean` | `compiler/IterationBound.log` | 0 | Actual TM2 bounded iteration with an explicit pointwise runtime estimate. |
| `RadixOrder.lean` | `compiler/RadixOrder.log` | 0 | Pure stable radix sorting correctness and permutation; supplied by subagent radix_order. |
| `BitEncoding.lean` | `compiler/BitEncoding.log` | 0 | Address-width, binary record encoding, and natural-key sorting correctness; supplied by subagent radix_order. |
| `RadixSortMachine.lean` | `compiler/RadixSortMachine.log` | 0 | Actual TM2 sorter with structured O((rows+1)*(width+1)^2) run bound; arbitrary-input declared bound remains quadratic. |
| `AdjacentScan.lean` | `compiler/AdjacentScan.log` | 0 | Actual globally linear TM2 adjacent-key consistency scanner; sortedness and common-width validity are separate premises. |

## Reproduction and dependencies

From the repository's `lean/` directory, run `lake env lean ../results/pequalnp-pilot-4b/L-lib-123/lean_setup/<Source>.lean` with the pinned toolchain and the prepared Mathlib cache. Never update the dependency pins. All scratch definitions needed by these sources are included in each file; there are no imports of another scratch file. Files sharing helper prefixes are standalone checks and should not be concatenated.

Mathlib and `PEqualNP.Defs` are existing project dependencies. Some L-lib-123 runtime helpers additionally import the existing tracked modules `PEqualNP.Library.Evasion.MBudget`, `PEqualNP.Library.Evasion.MTrans`, `PEqualNP.Library.Machines.IterMeasure`, or `PEqualNP.MetaComplexity.Helpers.Machines.Zip`. Their sources and transitive dependencies are already preserved in this repository; build those project modules with the pinned cache before checking the relevant standalone file. The exact direct imports are recorded in `validation.json`.

## Limits

No general short-trace circuit theorem, complete globally linear circuit verifier, or sufficiently fast conversion to the restricted one-writable-tape model was proved. The radix and scanner components cannot alone establish FP3 exponent savings.

## Independent checks

fp3_strategy independently reviewed CircuitCertificate, RadixSortMachine, and AdjacentScan. Independent block replay and restricted-controller reviews were also reported. The radix_order child supplied the pure sorting and encoding proofs.

This checkpoint contains checked sources, successful compiler output, and scope metadata only. It contains no solver trace, failed compilation probe, or proof-gap placeholder. It was preserved under the parent's explicit push-early instruction. lean_setup did not stage, commit, or push these files.
