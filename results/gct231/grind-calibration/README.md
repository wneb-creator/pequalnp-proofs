# Bounded Lean grind calibration: no successful proof

These attempts test Lean4.36.0's proof-producing commutative-ring solver on the already independently proved rowzero polynomial system. They do not prove any new theorem or the full posted statement.

- Original ordering,1,000,000 weighted ring steps,degree limit20: stopped at the sampled6GiB resident-memory limit after82.376seconds; no verdict.
- Reordered r²+2 hypothesis first,10,000 steps,degree6,3GiB resident cap: stopped after2.101seconds before diagnostics. This low cap does not distinguish import overhead from search and supports no search conclusion.
- Same reordered test,6GiB cap: ordinary tactic failure after7.617seconds. The reported limits were10,000 ring steps and polynomial degree6. The failure log prints sorryAx for the unsuccessfully elaborated declaration; this is not an accepted theorem.
- Reordered100,000 steps,degree8: stopped at60.620seconds with no verdict,peak4,736,188KiB RSS.

The prepared9-variable star-support source was not run. All successful rowzero proofs remain in the separate rowzero and f4-trace archives. Complete outputs and run metadata are retained here. The RSS runner samples every0.5seconds and terminates only its isolated process group; this is not a kernel hard RSS limit.
