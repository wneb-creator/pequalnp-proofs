# Calibration validation

These four files are exact copies of successfully compiled research diagnostics. They check individual finite checker equations using `decide +kernel`; they do not prove the full gap statement and have not been submitted to the repository checker. Their `#eval IO.eprintln` marker commands and string literals are diagnostic instrumentation only and must never appear in the final proof file. Exploratory imports must be inlined for the final single-file proof.

Every run used Lean 4.36.0, `LEAN_NUM_THREADS=3`, `lake env lean --profile -M5500 -j3`, and unbuffered standard output/error. Each run exited 0 without timeout. The complete stdout, stderr, and metrics JSON are preserved beside its exact source. `manifest.json` gives SHA256 hashes of each artifact and spells out each claim after expanding the local seed-list alias.

Peak RSS is the Linux `resource.RUSAGE_CHILDREN` maximum for a child/descendant process, not a sum across processes. Total elapsed time includes Lake startup and imports; kernel profile time is Lean's reported type-checking duration. Memory/time limits used for these diagnostics are not changes to the source or the repository's final checker configuration.

| Diagnostic | Kernel profile (s) | Total elapsed (s) | Peak RSS (KiB) | Lean exit |
|---|---:|---:|---:|---:|
| selector0_q35 | 4.09 | 6.59 | 3505884 | 0 |
| selector6_q35 | 8.17 | 10.85 | 4040888 | 0 |
| selector0_q7 | 5.05 | 7.70 | 3660676 | 0 |
| heavy_leaf67_hash79 | 10.70 | 13.42 | 4453220 | 0 |

All stdout contains only the instrumentation markers, profiling information, and the harmless warning that a Prop-valued `def` could be written as a theorem. All sources use ordinary kernel checking; none uses native_decide or adds an axiom. These results were measured on 2026-11-25 UTC.
