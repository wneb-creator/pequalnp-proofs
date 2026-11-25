# Reduced triangle finite-field diagnostic

The reviewed native sparse engine returned the reduced basis `[1]` over F1009 for the necessary reduced triangle-stratum equations. This is computational evidence about this finite-field system only. It is not a rational ideal-membership certificate, a complex-field contradiction, or a Lean proof of the gap.

- Start: 2026-11-25 11:49:23.934276 UTC.
- Result: `COMPLETED`, process exit 0, `unit_basis: true`.
- Wall time: 8.945474994998222 seconds; peak child RSS: 38,260 KiB.
- Limits: 600 seconds, 2,048 MiB address space, one thread, pair-selection parameter 32, 256 MiB per output file.
- Source: 12 variables, 26 equations, 686 terms. Source SHA256 `03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7`.
- Converted input SHA256 `39b6adda8c99cc7cd7087165de43cb774000e3e16bd1e0aed577e05f83b85c74`.
- Complete output basis SHA256 `c3cf6183caf060b9303583270b839fd8c32ca9a69d5563a7782731b581725f22`.

All 108 F4 rounds completed, followed by final basis reduction. The largest matrix reported by the engine was 4,415 by 6,170. The full log is retained, including its duplicated post-cleanup statistics; the first computational-data block reports the actual solve statistics.

The bounded-subset checkpoint engine is the already reviewed export-only derivative of the native engine. It preserves the original generators and exports at most one million additional terms. Both snapshots from this run are retained: initial snapshot sequence 1 and final snapshot sequence 2. The final snapshot appends the constant unit to the original 26 generators. The engine's result is recorded separately from checkpoint metadata; a checkpoint alone is not advertised as a certified basis.

The source reduction and sparse input were independently checked by c3 before the result was accepted; see [the source review](../triangle-twelve-review.md). `preflight.py` additionally reconstructs every input row and verifies exact rational equality up to its recorded primitive scaling, with no modular terms dropped. All 21 engine-provenance hashes were checked against the independently reviewed bounded-subset engine before launch. Its prior review is [here](../checkpoint-subset-review/REVIEW.md).

The archive includes the original source JSON, converter, runner, preflight, exact input, complete stdout/stderr logs, launch and result metadata, basis output, and both complete checkpoints. Engine binaries and vendor source trees are intentionally represented by their recorded hashes and existing provenance archive. No solver was rerun to create this archive. A subsequent independent archive/outcome review is kept outside this frozen directory.
