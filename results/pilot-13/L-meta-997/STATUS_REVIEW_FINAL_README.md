# L-meta-997: independent review and search record

No counterexample to the posted statement was found. The archived Lean results are helper lemmas and conditional cases, not a completed proof of the posted theorem. Every reported successful Lean probe uses only `propext`, `Classical.choice`, and `Quot.sound`. The official plain-file guard still reports `the file holds no theorem` for the partial file.

## Remaining proof obstruction

The compiled `LowDegree` and `UnionBudget` lemmas bound the union of selected heavy targets when their number is at most the NOT window size k. `UnionFree` additionally excludes gates whose singleton-triggered truth transfers to every input; this includes empty singleton-support prefix gates and the fixed-true NOT. Overlap multiplicity between targets still needs a separate bound and refunds. The unrestricted case with more than k large heavy targets remains open: cardinalities of boundary point/source incidences alone are insufficient. A complete proof must account for the AND gates used to separate shared signals, or find another global argument. Per-output Hall matchings and active-path/exit existence do not establish simultaneous inter-output capacity.

## Actual Boolean circuit searches

All families used were checked pairwise linear. Candidate circuits use exactly one NOT with the required minimum-weight window; whenever a SAT model was found, every CNF clause and the full Boolean truth table were checked, then the exact posted refund was counted.

| Search | Scope and outcome |
| --- | --- |
| MILP/CEGIS, two large heavy targets | Fixed-all-light prefixes: n14/tail4 variants infeasible; n16/tail6 and n18/tail8 timed out. n12 ordinary control also timed out, but its explicitly supplied feasible assignment satisfied every MILP constraint. |
| Evolutionary search, n14/37 gates | Two full-truth runs examined 6,150,976 candidates over 615 seconds. No exact candidate; nonzero best errors. |
| CaDiCaL, two large heavy targets | Fixed-all-light n12/tail2, n14/tail4, n18/tail8 models UNSAT on sampled assignments. These exclude only their fixed prefixes and gate budgets. |
| CaDiCaL, mostly free tails | Only three disjoint light ORs plus H/NOT fixed: n12/tail20 and n14/tail28 timed out at300 seconds each. n14 with every weight<3 assignment added also timed out at300 seconds. All UNKNOWN. |
| CaDiCaL, n17/k3/four heavy targets | Four size5 targets have distinct K4 pairwise intersection points.21 light triples come from three compatible matchings. Fixed-all-light prefix +8 tail gates UNSAT in20.9 seconds on200 samples. Ordinary16-tail control SAT in22.9 seconds; all131,072 inputs verified, refunds4, lhs83≤rhs90. |
| Positive controls | n8 relaxed-pair OR control, n12 exact SAT OR control (all4,096 inputs), and the n17 control above passed. An initial n12 SAT control omitted its witness and failed the parser assertion; corrected v2 passed and both logs are retained. |

A solver timeout is never recorded as infeasibility. No finite fixed-prefix UNSAT result proves the posted universal statement.

## Countermodels to weaker proof ideas

The switched examples invalidate certain blanket deletions of light charges; they still have more than enough actual gates. The small refined-overlap example does not place its shared gate in the actual heavy output ancestor cone. Neither is a posted counterexample.

The GF16 affine set circuit has256 singleton inputs and272 pairwise-linear size16 output sets:3276 set AND/OR gates versus4080 ordinary OR gates. It is exact only as a singleton-support set computation; higher-weight Boolean inputs create false positives.

The q11 switched/window construction has251 inputs,99 light and99 heavy outputs,1461 gates, and a relaxed weighted bound deficit321. Its light outputs are correct and its heavy outputs behave correctly on the specified window, but each heavy output has the wrong singleton support. It therefore fails the posted global output-correctness hypothesis.

Small exact set-only SAT probes support two-/three-color incidence bounds. They do not imply unrestricted direct sum:16 disjoint colors of16 points admit a168-gate set-code construction from free transversals, below240. Such set-code evidence must not be promoted to a full Boolean counterexample.

## Preservation

Five frozen manifests cover all selected scripts, compact results, complete stdout/stderr logs, and review records: `archive_manifest.json`, `extra_archive_manifest.json`, `sat_archive_manifest.json`, `late_archive_manifest.json`, and `post_union_archive_manifest.json`. Every payload hash was rechecked successfully after freezing. Generated CNFs/raw witnesses and copied full Lean review snapshots remain in scratch; reproducible scripts/parameters and useful full logs are archived instead. No searches remain active.
