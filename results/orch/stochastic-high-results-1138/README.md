# Completed high-eligibility search, 2026-11-25 11:37:50 UTC

No<=27-gate quiet witness was found. The best exact Fano function with both marked derivatives zero remains28 gates. The only captured ordinary truth-correct27 class has p7/Bplus14/Bzero0 and both derivatives true. These are bounded heuristic observations, not SAT/UNSAT or impossibility claims.

The single worker used the480-seed high-input configuration. Its first300 seconds were deliberately checkpointed with exit143 to add class-aware recording of ordinary function-correct circuits. The replacement changed only snapshot recording, not evaluator or fitness, and ran883 seconds to the original fixed cutoff, exiting0 after330,955,223 mutations. The random seed was unchanged, so the replayed initial search prefix is not independent coverage. Complete stdout/stderr logs and stop/start/exit metadata are retained.

The first segment has68 compact snapshots; the ordinary-aware segment has74. Every saved error signature was independently checked against all16,384 truth assignments and direct trace recurrence; no<=27 witness appears. Reproduce from this directory with:

- `python stochastic-result-verify.py first300 stochastic-high-phase`
- `python stochastic-result-verify.py recorded stochastic-high-recording`

The input high-p seeds include deliberately redundant star squares. Runtime CSE can remove squares unrelated to the marked edge and reduce eligibility; this weakens high-p exploration despite preserving function and marked traces. A different masked41-gate p14 scaffold that survives CSE is preserved in the separate masked-controls archive. No claim of exhaustive high-p coverage is made.

All files are immutable, with hashes and byte counts in MANIFEST.json. The stochastic CPU slot was released at completion for targeted SAT work; no subsequent active output is included.
