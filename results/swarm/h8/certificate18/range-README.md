# Helper 8 verified range

The kernel checked all 622 states with indices 4608 through 5229, inclusive. `H8Range.lean` proves the aggregate theorem `PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8.checked`, with an explicit lower bound on the index. The index upper bound comes from `Fin 5230`.

The five source proofs cover four blocks of 128 states and a final block of 110. Each theorem uses `listPieces_all` depth 5, making separate kernel auxiliary lemmas for groups of three or four states. The checker remains the frozen `Replay.DirectMode.Packed.checkNode`.

Build modules in the manifest order after the frozen packed-checker stack. `H8Chunk4992` and `H8Chunk5120` are small import wrappers for the proofs built in parallel as `H8Parallel4992` and `H8Parallel5120`; preserve those dependencies. For eventual standalone source flattening, include each actual proof body once and discard the import wrappers.

The aggregate and all five chunk theorems have only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. Independent source review approved the generic range assembly and exact interval coverage. Complete stdout, stderr, source hashes, and per-process metrics are included.

Total range replay wall time was 657.16 seconds (10.95 minutes). Peak proof-process RSS was 4,186,404 KiB. The driver was deliberately paused while an independent block completed, so the recorded wall time for `H8Chunk4864` includes coordinator waiting; its CPU metrics remain exact. The two parallel proofs have separate timing reports.

This artifact proves only the assigned range. It does not claim the full 5230-state closure or the exact posted gap.
