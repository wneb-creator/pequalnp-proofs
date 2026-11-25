# Counterexample search for L-meta-2373

No19-gate witness has been found. None of these searches is a lower-bound proof.

| Search | Budget | Result |
| --- | --- | --- |
| Ordinary19-gate stochastic, seed2373 | 600s | 2,120,500,000 evaluations; best6 false negatives |
| Ordinary19-gate stochastic, seed23731, temperature multiplier10 | 600s | 1,671,250,000 evaluations; best9 false negatives |
| Signed19-binary-gate stochastic, seed237311, multiplier2 | 600s | 2,060,500,000 evaluations; best9 false negatives |
| Signed18-binary-gate stochastic, seed237318, multiplier2 | 600s | 2,473,250,000 evaluations; best15 false negatives |
| Global19-gate SAT, firstAND(edge) | 600s | UNKNOWN |
| Global19-gate SAT, firstNOT(input) | 600s | UNKNOWN |
| Global19-gate SAT, firstOR(nonedge) | 600s | UNKNOWN |
| Global19-gate SAT, firstOR(nonedge), roots last, at most1NOT | 600s | UNKNOWN |
| Unseeded20-gate monotone SAT positive control | 120s | UNKNOWN |
| Unseeded20-gate monotone SAT positive control, roots last | 120s | UNKNOWN |
| Incremental localSAT, all1024 rows | 600s | 286 neighborhoods:1 UNSAT,285 UNKNOWN; no SAT |
| Incremental localSAT,91-row promise | 600s | 1118 neighborhoods:27 UNSAT,1091 UNKNOWN; no SAT |

A fixed20-gate reference circuit was independently evaluated on all1024 rows and SAT-validated on all1024 rows. Both incremental localSAT runs also passed a fully fixed20-gate positive control before searching. The ordinary best19-gate candidate has exactly six false negatives and zero false positives. It is not equal to Petersen with any single edge deleted.

The signed-basis run grants complemented gate inputs and outputs for free. A signed witness would require explicit NOT-cost accounting before it could refute the original statement. normalize_signed.py minimizes inserted NOT gates over all phase choices for the fixed signed DAG and then removes semantically duplicate/dead gates; it validates every converted circuit on all1024 rows. Its positive20-gate control preserves20 ordinary gates and matches the target exactly.

synth.py uses one-hot operation and source selectors. Source0 is free false; sources1..10 are primary inputs. Optional live/ordered/irredundant/root-last/NOT-count restrictions are search heuristics. UNSAT under these restrictions is not asserted to cover arbitrary circuits. The roots-last and lex-order restrictions may interact, so their combination is especially only a search filter. Initial91 rows are all76 independent sets plus15 edges; every candidate is checked on all1024 rows and violating rows are added. The two outputs before the finalOR must also be incomparable before a candidate can refute L-meta-2373.

local_sat.py seeks one identity gate in a20-gate circuit while changing4–10 gates around known20-gate references. Its UNSAT answers only exclude individual neighborhoods. Global SAT positive-control difficulty led us to retire broad synthesis rather than interpret timeouts as evidence of impossibility.

Complete stdout/stderr logs and source hashes/bytecounts are preserved in counterexample-manifest.json. cadical_wrap.cpp creates a small C ABI wrapper over the pinned Lean toolchain bundled libcadical.a, linked to its libc++ runtime; the shared library itself is not preserved. No downloaded solver source or credential is used.

All runs finished. No exact counterexample was found. Across the four stochastic runs there were8,325,500,000 heuristic candidate evaluations; this is not an exhaustive census. The best signed18 candidate becomes an18-gate monotone circuit after phase normalization and misses15 target-positive assignments. The phase converter also passed200 independently generated small signed circuits, checked on all1024 truth rows each (normalize-random-validation.txt). Broad globalSAT expansion is retired because even the unseeded20-gate positive controls remained UNKNOWN.
