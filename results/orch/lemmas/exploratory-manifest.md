# Exploratory computation archive for L-meta-4675

This archive preserves completed work from the semantic, structural, and algebraic routes. No experiments were rerun. Full source snapshots, output streams, solver inputs, and models are under `exploratory-logs/`; exact hashes and scopes are in `exploratory-manifest.json`.

| Experiment | Status |
|---|---|
| orfree-c6-four | UNSAT |
| orfree-c6-validation | SAT |
| orfree-fano-nineteen | UNKNOWN_TIMEOUT |
| orfree-fano-validation | SAT |
| orfree-pendant-five | UNSAT |
| orfree-pendant-validation | SAT |
| orfree-c8-six | UNKNOWN_TIMEOUT |
| orfree-c8-validation | SAT |
| structural-optimal-2-2 | NO_PAIR_DIRTY_AT_REFERENCE_SIZE |
| structural-optimal-2-3 | NO_PAIR_DIRTY_AT_REFERENCE_SIZE |
| structural-optimal-2-4 | NO_PAIR_DIRTY_AT_REFERENCE_SIZE |
| structural-optimal-3-3 | NO_PAIR_DIRTY_AT_REFERENCE_SIZE |
| structural-optimal-1-5 | NO_PAIR_DIRTY_AT_REFERENCE_SIZE |
| structural-cycle-smt | UNSAT |
| structural-pendant-smt | UNKNOWN_TIMEOUT |
| structural-pendant-normal-smt | UNKNOWN_TIMEOUT |
| structural-pendant-pivotal-smt | UNKNOWN_TIMEOUT |
| structural-reader-family | FINITE_ASSERTIONS_COMPLETED |
| semantic-bank-obstruction | FINITE_ASSERTIONS_COMPLETED |
| semantic-cluster-obstruction | FINITE_ASSERTIONS_COMPLETED |
| semantic-cluster-lambda-obstruction | FINITE_ASSERTIONS_COMPLETED |
| algebraic-residual-eval | FINITE_ASSERTIONS_COMPLETED |
| algebraic-bank-obstruction-eval | FINITE_ASSERTIONS_COMPLETED |

The unbounded-AND model excludes four OR gates for C6 and five for C6 with a pendant edge. Fano19-OR and C8 six-OR searches timed out UNKNOWN. Their pinned next-size controls passed full truth-table replays. These are finite computational results, not Lean certificates or a generic OR-count theorem.

Structural enumeration tested pair-dirty ANDs at size |E|+tau(E)-1 on specified splits through six inputs. Its semantic/op/colour memoization does not preserve wiring, so it supports no lambda-count claim. The inherited “Separate bounds violated” footer is inert and must be ignored. The C6 eight-gate pair-dirty SMT query is UNSAT; all three nine-gate pendant variants are UNKNOWN. The latter add different normalization premises, documented individually.

The reader family and13-gate shared-bank example are deliberately nonminimum. The19- and23-input cluster examples have edge-inactive payloads and fail normalized minimum-circuit assumptions. None refutes L-meta-4675. The corrected eight-gate double-star has residual sum5=5; it only refutes a separate cover-charge inequality without minimum.

Every archived JSON is the complete original stdout report. Empty stderr files are retained. Source-level inputs are preserved, not only log excerpts. Binary executables, caches, process listings, active Lean work, and credentials are excluded. Author confirmations and limitations are recorded in the machine-readable manifest.
