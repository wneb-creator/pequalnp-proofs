# Computational manifest for L-meta-4675

No Lean proof or refutation is claimed. Machine-readable scopes, commands, and SHA-256 hashes are in `counterexample-manifest.json`. Complete original logs and exact generated SMT inputs are in `counterexample-logs/`. All runs below terminated by2026-11-25 18:08:28UTC.

| Experiment | Status | Completeness |
|---|---|---|
| total-2-3 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| total-3-3-5 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| total-3-3-6 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| total-3-3-7 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| total-2-4-5 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| total-1-5-4 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_STATE_SYMMETRY |
| separate-3-3-6 | NO_COUNTEREXAMPLE | EXHAUSTIVE_WITH_SOUND_DOMINATION_AND_COUNT_PRESERVING_STATE_SYMMETRY |
| raw-crosscheck | ALL_TARGET_MINIMA_MATCH | EXHAUSTIVE_RAW_HISTORIES |
| fano-exact-certificate | VALIDATED | EXHAUSTIVE_INSTANCE_CERTIFICATE |
| fano-initial | NO_WITNESS | HEURISTIC_NOT_EXHAUSTIVE |
| fano-diverse-26 | NO_WITNESS | HEURISTIC_NOT_EXHAUSTIVE |
| fano-diverse-or19 | NO_WITNESS | HEURISTIC_NOT_EXHAUSTIVE |
| fifty-five-graphs | NO_WITNESS | HEURISTIC_NOT_EXHAUSTIVE |
| fano-bv-known27 | SAT | ENCODING_POSITIVE_CONTROL |
| fano-bv-26 | UNKNOWN_TIMEOUT | INCONCLUSIVE |
| fano-onehot-known27 | SAT | ENCODING_POSITIVE_CONTROL |
| fano-onehot-26 | UNKNOWN_TIMEOUT | INCONCLUSIVE |
| residual-minimum-2-2 | ALL_THREE_BOUNDS_PASS | EXHAUSTIVE_WITHIN_SPECIFIED_BOUND_SIZED_SCOPE |
| residual-raw-2-2-5 | ALL_THREE_BOUNDS_PASS | EXHAUSTIVE_RAW_HISTORIES |
| residual-raw-2-3-5 | ALL_THREE_BOUNDS_PASS | EXHAUSTIVE_RAW_HISTORIES |
| large-lam-raw-3-3-5 | ALL_THREE_BOUNDS_PASS | EXHAUSTIVE_RAW_HISTORIES |
| large-lam-double-star | SAT_SEPARATE_BOUND_COUNTEREXAMPLE | EXACT_FINITE_INSTANCE |
| large-lam-double-star-sum | UNSAT_PINNED_CONTROL | EXACT_FINITE_INSTANCE |
| large-lam-eight-sum | UNKNOWN_TIMEOUT | INCONCLUSIVE |
| large-lam-dag-3-3-6 | ALL_THREE_BOUNDS_PASS | EXHAUSTIVE_WITH_FULL_WIRING_DAG_SYMMETRY |

The raw largeLam run covers696220624 histories through five gates on3+3 inputs. The full-DAG-symmetry run covers all circuits through six gates on that split, using1376245484 representative-prefix visits. It retains every wiring edge and gate multiplicity; no truth-table state merging is used.

`all_active` means structural output-cone inclusion, not the stronger edge-pair activity. The near-bound subset uses size <= |E|+tau(E)-1+2, not an assumed minimum theorem.

The pinned eight-gate double-star refutes the separate residual cover bound without minimum: tau(U)=2 > c+j=1. Its sum bound holds at equality five. It is not a refutation of L-meta-4675.

All three unpinned SMT searches returned UNKNOWN: Fano bitvector300.210792343s, Fano one-hot600.125799067s, and8-gate SUM residual300.230553444s. Their timeouts establish no lower bound. Pinned SAT/UNSAT controls concern only those pinned circuits.

Preliminary invalid forward-reference SMT logs, a superseded separate-count run, and a failed exploratory Lean file lookup are archived and explicitly excluded from evidence. Heuristic failures remain inconclusive.

Historical `counterexample-residual.py` output says “Optimal circuits” but locally checks size equality to |E|+tau(E)-1. Its60 histories include36 TopForm histories; the independent raw crosscheck separately excludes smaller circuits on2+2 inputs.

Both Fano SMT searches require every nonoutput gate used and exclude repeated-input OR gates. The one-hot26-gate search also imposes at most19 OR gates and at least one dirty AND. These are explicit encoding restrictions.

Sources use C++17/Python3. SMT drivers use the installed Z3 shared library through ctypes. Some historical sources changed instrumentation, so current visited counts can differ; archived SMT files preserve exact solver instances. No binaries, Python cache files, or credentials are included.
