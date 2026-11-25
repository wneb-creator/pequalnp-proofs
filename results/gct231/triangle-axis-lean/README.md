# Checked conditional triangle-axis certificate

`ThreeByThreeAxisCertificate.lean` proves that four displayed polynomial equations in three complex parameters cannot hold simultaneously. Its exact rational polynomial combination yields the nonzero constant 4,214,784, and Lean checks both that identity and the contradiction. The theorem retains all four equations as explicit hypotheses. This archive does not identify those hypotheses with the full gap statement or claim a global complex-subspace contradiction.

The source is byte-identical to the independently reviewed input from `triangle_concept/ThreeByThreeAxisCertificate.lean`: SHA256 `f453366b19430a626696520b30cdcbefbd2131b6aa4cc32606fa2c7beeb89a22`. No theorem statement or proof was altered. Its narrow Mathlib imports and scoped heartbeat limit are retained. See [the algebraic review](../three-by-three-axis-review.md).

Final source compile (`build02`): PASS, exit 0, empty complete log, 4.092972843998723 seconds, sampled peak process-group RSS 2,667,696 KiB. The separate axiom driver is exactly the source followed by one `#print axioms` command. It passed in 4.6551066510000965 seconds with sampled peak RSS 2,662,940 KiB and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Both runs used the preserved serial runner with a 240-second wall deadline and a sampled 4,096-MiB process-group RSS ceiling, sampled every half second. This is a monitor, not a kernel-enforced hard resident-memory limit. Core dumps were disabled. Every stdout/stderr log and runner metadata file is retained.

Diagnostic history: an initial trial unnecessarily replaced the current `Mathlib.Basic.Complex.Basic` import by its older `Mathlib.Data.Complex.Basic` alias. That trial compiled but produced a deprecation warning. The original preferred import was then restored byte-for-byte for `build02` and the axiom audit. The alias trial source and full `build01` logs are retained solely to explain that warning; they are not the final source.

The original source copy, final source, diagnostic alias variant, exact axiom driver, monitor, and complete logs are all included. Independent red-team review of the compiled artifact and archive is recorded separately so this manifest can remain frozen.
