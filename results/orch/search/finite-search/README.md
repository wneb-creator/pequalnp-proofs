# Finite-search research archive

These are original scripts and complete diagnostic logs from the L-meta-2602 search. They are research artifacts, not a proof of the posted lower bound. No 64-gate plane counterexample was found.

- `local_sat.py`: exact AND/OR window encoding with distinct earlier fanins, optional adjacent topological ordering, formal derivative channels, and optional exact AND count. `decode_local_sat.py` independently evaluates a decoded plane circuit on the 52 edge pairs, 704 maximal independent sets, and both singleton traces. CNFs are deliberately omitted; profiles recreate them.
- `local_synth.py`, `prepare_local_profile.py`, `local_hill.cpp`: profile construction, older MILP approach, and heuristic mutation search. Solver timeouts are inconclusive. `tree_window.py` exposes nine free pair-OR prefix wires to a local tree resynthesis problem.
- `theta_extend.py`, `theta_extend_virtual.py`, `theta_mutate_once.py`, `theta_build65.py`: theta4 embedding, compatible prefix OR-tree variants, direct rewiring, and a verified 65-gate completion. The fixed source-pool lower bound rules out seven OR-only injections for the tested 675 seeds; it is not a lower bound for arbitrary circuits.
- `search.py`, `search4.py`, `synth.py`, `hill.cpp`, `drop_one.py`: initial small-graph enumeration, MILP, heuristic circuit mutation, and single-gate bypass tests. When comparing a path counterexample, specify the marked edge: central-edge and leaf-edge double traces have different costs.
- `theta3_or_prepare.py`: complete 4×4 C4-free graph census and preparation of the nine-edge theta3 OR-count test. A relaxed shadow profile allows higher minterms and is only a diagnostic.

`data/plane65-witness.json` is the absorption construction (13 AND, 52 OR). The theta construction uses 14 AND, 51 OR; both have 65 gates. `data/tree10-double12-witness.json` exhibits a bipartite tree with ten edges, cover number three, and a 12-gate double-trace circuit with three AND/nine OR. Minimality of those 12 gates is not proved: the ordinary 11-gate search timed out.

Each ordinary `.log` is the complete captured stdout/stderr. `logs/theta-direct-mutations.jsonl` losslessly stores all 675 complete small mutation logs as JSON strings with their source filenames. Files retain their original scratch paths in arguments and code; restore the `profiles/` and `data/` files under `/tmp/oec/pequalnp-pilot-65/finite-search/` to reproduce, or explicitly change that nonsemantic path. Theta seeds and their generation scripts are in the sibling `status-review` archive. No binary executable is included. The two-roots certificate bundle is the explicit exception to omitted generated CNFs.

`MANIFEST.json` records byte lengths and SHA-256 hashes of all archived files except itself. Review diagnostic outcomes directly in the complete logs and `results/orch/finite/sat_summary.json`; an interrupted or UNKNOWN run proves nothing.

Theta3 OR-count follow-up: both the exact graph and relaxed pair-shadow searches with seven OR/eight AND gates timed out after 180 real seconds (exit 0). Neither is an UNSAT result. A pinned ordinary twelve-gate construction with four AND/eight OR gates passed the new cardinality encoding in 0.01 seconds; `theta3_control.py` recreates the pinned instance and independently verifies its full 256-row truth table. The bounded eight-AND search does not cover arbitrary numbers of AND gates.

The `two-roots/` follow-up preserves a finite exact-function UNSAT diagnostic, a counterexample to the weaker clean-fragment route, positive controls, and a completed C8 plane augmentation attempt. Its ASCII LRAT certificate is a research artifact and has not been kernel-checked; see that directory README for scope.
