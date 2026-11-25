Expanded exactly-one-NOT local SAT neighborhoods

This parameter-only extension of the reviewed one-not-local/focused.py uses20trials,45seconds per trial, a900-second overall budget, and one million conflicts per solver round. Requested relaxed sizes are8,10,12,14; mandatory adjacency expansion can increase them. The encoder, exact-one-NOT requirement, bypass-gate condition and full1024-row candidate validation are unchanged. Gates outside each recorded neighborhood stay fixed. Exact source diff and both hashes are preserved.

The run completed20trials: one local UNSAT,19UNKNOWN, zero candidates. Total897.41seconds; exit0. The known20-gate positive control returned SAT on all1024rows. This establishes no global lower bound and no Lean-certified UNSAT. Every trial records its exact seed, skipped gate, relaxed set, limits and complete solver-round outcomes. Full stdout/stderr is preserved together in full-log.txt.

The source still names the original prepared scratch directory for imported helpers. Those helper sources are already archived in the parent search directory (synth.py, local_sat.py, cadical_wrap.cpp); reproducing the SAT runs requires rebuilding the same solver wrapper/environment. No solver binary or credential is included.
