# Verified tail and combined late range

The new kernel checks cover all 256 states from 4352 through 4607. `H8TailRange.lean` proves `PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail.checked`: for `i : Fin 5230`, the explicit bounds `4352 ≤ i.val` and `i.val < 4608` imply the frozen `Replay.DirectMode.Packed.checkNode i = true`.

`H8LateRange.lean` combines that result with the previously verified 4608–5229 range. Its theorem `Helper8Tail.checked_late` requires only `4352 ≤ i.val`, since `Fin 5230` supplies the upper bound. This covers 878 consecutive late states. Together with the separate early 256–767 proof, helper 8 contributes 1,390 verified states.

Build the seven modules in manifest order after the frozen packed checker and the earlier `delivery-h8-range` bundle, which supplies `H8Range`. Both new 128-state proofs use depth-6 `listPieces_all`, giving two-state kernel auxiliary lemmas. The exact new 256-state receipt remains separate from the combined theorem.

All four tail builds and both combined-range builds passed. The four axiom receipts contain only `propext`, `Classical.choice`, and `Quot.sound`. Source hashes and complete stdout/stderr are included. Independent source and compiled-metadata review approved the exact hypotheses and found no foreign exports; final manifest review is performed separately.

The new 256-state replay completed in 267.77 seconds, with a peak proof-process RSS of 3,985,880 KiB. This driver reaps children in completion order, so the reported per-process wall, CPU, and RSS values describe their own executions. The combined theorem and axiom report took a further 3.27 seconds of build time. The Python driver is specific to the original job paths; the manifest module order gives the portable reproduction route.

These are verified ranges of the frozen checker. This delivery does not claim the full 5,230-state closure or the exact posted gap.
