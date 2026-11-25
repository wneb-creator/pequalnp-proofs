# Interrupted 12-gate stress-graph heuristic, version 2

This frozen run was interrupted before its requested 600 seconds completed. Its result is UNKNOWN: no correct circuit was recorded, and the run proves no lower bound or refutation of L-meta-1772.

The exact script, complete available stdout/stderr log, best saved candidate, and replay encoding are preserved here. No finished event appears in the log. The final elapsed time, iteration count, and restart count were not recorded. The last progress event records 390.016844803 seconds, 210,428,000 iterations, and 10,521 restarts; these are not completion totals.

The search uses an eight-vertex, ten-edge graph obtained by subdividing four edges of K4. It requests 12 binary monotone gates, starting from random 13-gate star-cover circuits. The recorded seed is 6602. The best saved candidate has one scored test error and six full truth-table errors among all 256 inputs, all false negatives. Its status is `HEURISTIC_CANDIDATE_NOT_A_CORRECT_CIRCUIT`.

`validation.json` records an independent reevaluation of the saved circuit and replay encoding. All gates are legal binary AND/OR gates reading only earlier wires. The 19 tests are exactly the ten edge inputs and the nine maximal independent inputs. For a monotone circuit, passing all these tests characterizes the graph function. The search also asserts equality on all 256 inputs before recording an exact witness. No zero-score candidate was recorded.

Version 2 fixes the earlier script's final-mutation boundary bug by checking the last accepted candidate before restarting. This is still a randomized, incomplete search; duplicate operands and unused gates are allowed, the output is the final gate, and no search outcome here establishes UNSAT or optimality. Even a correct saved circuit would require separate Lean checking and would not automatically refute the ownership statement.

The replay encoding is a byte-for-byte copy of `sat-stress12restartbase-12-encoding.json`. Its four fields used by the heuristic (`n`, `gate_count`, `edges`, and `tests`, including list order) were also checked equal to both archived-run alternatives named in `validation.json`. No claim is made that replay will stop at the interruption point.

From this directory, using Python 3 and only its standard library:

```sh
python3 rewire_search_v2.py --encoding stress12-encoding.json --seconds 600 --seed 6602 --output /tmp/oec/pequalnp-pilot-66/stress-heuristic-replay-best.json
```

The wall-time cutoff depends on machine speed. No solver binary, credentials, or installation files are included. `sha256.json` hashes the six other files in this directory.
