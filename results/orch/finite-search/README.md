Finite search artifacts for L-meta-2584

These are computational experiments and solver outputs, not Lean proofs of the gap or of the reported lower bounds. The exact queries, source generators, control models, and complete stdout/stderr are preserved. SAT/UNSAT claims retain the symmetry and minimum-circuit reductions documented in second-pass-report.txt and the generators. Timeout or terminated runs establish no SAT/UNSAT conclusion. No counterexample to the posted existential replacement statement was found.

The checked C6 witness is included in the main Lean helper file; the general statement remains unproved. Solver binaries, downloaded packages, credentials, and caches are deliberately absent. manifest.json records exact hashes and byte counts of these archived task artifacts.

Random-search counting clarification from independent review: the code rejects duplicate live wire functions within each sampled circuit, but it does not deduplicate circuits across trials. The reported43,359 and302,844 counts are qualifying samples, not counts of mutually distinct circuits. Original reports and stdout are preserved byte-for-byte for traceability.
