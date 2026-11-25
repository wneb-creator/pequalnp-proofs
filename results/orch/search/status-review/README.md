# L-meta-2602 search archive

Status: **no proof or refutation of L-meta-2602 was found by these searches**. This directory preserves selected programs, complete run/solver logs, and useful witnesses. It is research material, not a single-file proof submission. `MANIFEST.json` records SHA-256 hashes of the 172 copied source artifacts (2,324,918 bytes); no binaries or large CNFs are included. The CNF generator is included.

## What the evidence supports

- `bowtie-8-double-1-2.witness.json` is an eight-gate double-read circuit for two triangles sharing a vertex. Its full truth table and traces check. The seven-gate ordinary SAT encoding returned UNSAT. This disproves a generic minimum-circuit/no-double conjecture, **not the bipartite plane statement**. Solver minimality has not been certified in Lean here.
- `tree10-double12-witness.json` (from finite_search) is a bipartite tree with 10 edges, vertex-cover size 3, and a 12-gate double-read circuit (3 AND, 9 OR). Its full truth table checks. It refutes the generic claim that AND/OR count equalities alone preclude double-read. **No minimality proof is claimed for this circuit.**
- `polarized-225.json`, `polarized-227.json`, and `mixed-027.json` are valid 17-gate double-read circuits for the four-path theta graph. The generators produce the 18 association variants and 657 mixed variants summarized in the index files; these 675 repetitive witness files are regenerable and mostly omitted.
- `plane65-witness.json` is the checked **65-gate** plane double-read witness from finite_search. It lies above the gap's bound and therefore is not a refutation.
- Exhaustive finite enumeration programs report: no five-gate double-read for the four-variable local kernel; no four-OR implementation of C6 even with free AND; and no two-AND implementation of the 120 considered C4-free 3-by-3 bipartite graphs with cover size 3. These are independent program results, not Lean certificates. `small_sat.py` and its complete logs also preserve small C5/C6/house/K4/bowtie results.
- `theta-ranking-cover.json` reports source-cover lower bound at least 8 for all 675 fixed theta cores: 558 have bound 8, and 117 have no covering source-mask combination (sentinel 99), within the specified prefix/port-OR injection model. This obstructs seven such injections, **not arbitrary 64-gate circuits**.

## Inconclusive searches

The mutation/annealing programs, theta SAT timeouts, and semantic-DAG DP did not find an improvement. Their failure is **inconclusive**. The strongest DP run retained eight alternatives per 17-row truth/two-trace signature, tracked actual shared-gate union costs, and explored 1,984,437 candidate DAGs / 2,679,820,725 pairs in 180 seconds. It used heuristic frontier and representative pruning; equal-signature gates were not universally deduplicated, and a distinct-copy AND construction was included. No UNSAT conclusion follows.

## Reproduction and validation

Run `python3 verify_witnesses.py` from this directory for an independent check of archived witness gate legality, full small-graph truth tables, and both directional traces. For the plane witness, the script regenerates all 704 maximal independent sets and checks them plus all 52 edges. Monotonicity makes these critical rows sufficient for full functional equality.

The archival search programs retain their original absolute scratch paths; edit those path constants or recreate the recorded scratch layout before rerunning them. `small_sat.py --help` documents its arguments; it expects CaDiCaL at the recorded toolchain path. The self-contained C++ DP takes `tree-cross9.profile SECONDS FRONTIER_WIDTH`; compile with `g++ -O3 -std=c++17 semantic_dag.cpp -o <scratch executable>`. Complete diagnostics are preserved rather than excerpted. SAT UNSAT statuses depend on the encoder and solver, and have no independent proof-certificate validation in this archive.
