# Verified early range 256–767

`H8EarlyRange.lean` proves `PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Extra.checked_early`: for `i : Fin 5230`, assumptions `256 ≤ i.val` and `i.val < 768` imply the frozen `Replay.DirectMode.Packed.checkNode i = true`.

All four128-state source proofs, both range aggregates, and six final axiom reports have built successfully. Each source proof uses `listPieces_all` depth6, generating separate two-state kernel auxiliary lemmas. The axiom receipts contain only `propext`, `Classical.choice`, and `Quot.sound`.

Build the nine modules in manifest order after the frozen packed checker. The smaller256–511 theorem and checkpoint receipt are preserved separately. Complete source hashes, stdout, stderr, and metrics are included. The job-specific Python driver records the original parallel schedule; reproducing the modules in manifest order is the portable build route.

Total wall time was1059.74seconds (17.66minutes). Peak proof-process RSS was4,652,124KiB. The driver waits for each pair of children in order, so individual wall values are completion/reap intervals and can overstate the faster child’s execution time; per-process CPU and peakRSS measurements remain exact. Overall receipt wall time is exact.

This artifact proves512 states. Together with the separate4608–5229 delivery, helper8 has1134 assigned states verified. Neither package alone claims the full5230-state closure or the exact posted gap.
