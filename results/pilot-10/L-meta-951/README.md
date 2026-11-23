# L-meta-951 partial research snapshot

These artifacts are preserved under the user instruction of 2026-11-23 to push every compiled partial result. They are not an accepted proof or refutation of L-meta-951, and no proof PR is being opened for this snapshot.

The exact posted proposition is in `statement-meta-951.txt`. The 32 Lean files in `manifest.json` each completed `lake env lean <file>` with exit code 0 against the pinned project. Their complete final diagnostics are preserved beside them; empty logs mean compilation emitted no diagnostics. The manifest states the additional hypotheses or limited scope of each result. Some files duplicate supporting lemmas so they can compile independently.

`GoodObstruction951.lean` and `PaschHardPiece.lean` disprove attempted intermediate lemmas. Neither refutes the posted statement. The K5 wrappers use existing Outside theorems and are research artifacts, not final submission files. Some copied comments also require the repository plain-file cleanup before any final submission.

The checker executable and project definitions built successfully. The repository checker has not accepted a full L-meta-951 proof or refutation. See `checker-status.txt` and the complete infrastructure logs. Historical audit notes describe the state at their recorded audit time.

No cleanup pass has been performed on a final proof because no full proof exists. All copied Lean sources are byte-for-byte copies of the sources that produced the recorded successful runs.

Additional solver sources and complete finished-run logs preserve the finite searches. An SMT UNSAT result concerns only its stated finite family and encoding; it is not a Lean certificate. A timeout or UNKNOWN result is inconclusive. The completed stochastic searches found no witness and prove no lower bound. Mathematical notes outside the Lean files remain informal arguments, with their limitations stated in the documents.

Sub-agents: independent_search; literal_not_restriction; independent_theory; proof_strategy; single_not_reduction; toolchain_setup; fresh_full_proof.
TIMING total=94 subagents=7

Frozen generated SMT inputs are additionally preserved under `queries/` as gzip files, with original SHA-256 hashes in `queries/manifest.json`. They are finite solver inputs, not Lean proof certificates. Inputs for still-running E3 queries are added only when those runs finish.
