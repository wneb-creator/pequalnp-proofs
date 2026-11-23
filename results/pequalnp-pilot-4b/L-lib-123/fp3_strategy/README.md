# L-lib-123 — checked partial results

No universal short trace representation or strict exponent-saving simulation was proved. The posted FP3 statement remains unproved and unrefuted.

- `AltLemmas.lean`: Boundary lemmas and fixed-exponent constant-absorption obstruction.
- `FlattenBudget.lean`: Resource arithmetic for recursively flattened alternating verification.
- `GrammarBound.lean`: Distinct-substring lower bounds for binary concatenation grammars; no bound for general arithmetic or program summaries.
- `StackTrace.lean`: Exact local characterization of list-stack execution, including initial stacks.
- `StackChallengeFull.lean`: Self-contained mate-free three-block stack challenge characterization.
- `CheckpointReplay.lean`: Fixed-checkpoint local replay gluing and existence equivalence.
- `BlockMinimum.lean`: Canonical block minima and interval decomposition.
- `AltEncoding.lean`: Typed three-block encoding and self-sized parsing semantics; no total verifier runtime theorem.

The complete successful compiler logs are preserved beside each source; empty logs mean the compiler emitted no stdout or stderr. `manifest.json` records exact source hashes and the preservation recheck. These files do not constitute a completed target proof, and the posted-statement checker has not accepted them as one.

The accompanying reports distinguish checked helper lemmas from unproved strategies and restricted finite searches. No failed diagnostic logs or large SAT artifacts are included.

KIT-MESSAGE-ID: msg-9574e75c4a2464ba7a74e928
