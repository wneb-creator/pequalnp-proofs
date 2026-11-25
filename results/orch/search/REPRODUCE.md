# Fano circuit search, pequalnp-pilot-94

These are computational search artifacts for L-meta-2583, not Lean proofs. No counterexample has been found. The known READ1 optimum is 27 gates.

`circuit_cgp.cpp` embeds either the exact 27-gate star circuit or a correct 29-gate dirty circuit into 42 slots, leaving inactive gates as workspace. It accepts only mutations preserving the 58 minimal-positive/maximal-negative test vectors. For monotone circuits these characterize the complete Fano incidence function. The objective counts only gates reachable from the output. Any candidate with at most 26 reachable gates is emitted after pruning and must be checked independently on all 16,384 inputs.

`circuit_cgp_readtrack.cpp` additionally tracks squarefree proofs for all 21 incidence pairs in parallel, and logs the first correct 27-gate circuit lacking READ1 on any edge. It leaves the primary size objective unchanged.

`COMMANDS.json` records exact original argument arrays. The machine-specific scratch prefix can be replaced with this directory when rebuilding; binaries are intentionally excluded. Both controls recovered exactly 27/29 reachable gates and passed independent full truth-table verification. The tracked READ1 masks also matched independent per-edge proof-state evaluation.

The first CGP evolution reached correct circuits of sizes 29, 28, and 27. All are preserved with validation in `cgp-verified-evolution.json`; the 27-gate result is READ1 and every AND is safe. A failed or time-limited heuristic search proves no lower bound.
