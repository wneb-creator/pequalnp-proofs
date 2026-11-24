# Alternative six-point core with interacting dirty helpers

This is a heuristic search for a 28-gate monotone circuit on the independently checked 19-input, 24-edge alternative6 core. The standard local circuit has 29 gates. A 28-gate witness would imply a 124-gate full-plane counterexample through the separately Lean-checked AlternativeLiftComplete theorem. No such witness has been found.

The source-set model cycles through seven, eight, nine, and ten AND rows, with one or two shared linear OR helpers. Some initializations use the interacting two-dirty matching identity from the global search: two dirty products intersect to represent two induced matching edges. The initializer replaces those two edge contributions in the six stars and has exactly 35 gates. This is a valid warm start above the target, not a counterexample.

The MatchingNear variant adds only artifact recording. It preserves up to 24 near misses of at most 28 gates, one to four wrong extremal tests, and at least two active dirty AND rows, separately from the ordinary near-miss buckets. Every such artifact is explicitly marked INVALID, includes its exact wrong tests, and is physically expanded and replayed. No objective, mutation, or random choices change in this variant.

All function checks use the complete 24 positive and 64 negative extremal assignments. Author calibration checked 1,440 baseline/mutant expansions for physical gate cost, topology, and scalar semantics. Independent review checked another 100 baselines and the recording-only delta. The concrete 35-gate fixture is calibration data only. Solver-free stochastic search supplies no UNSAT or lower-bound conclusion.

Planned command, from repository root:
```
python3 results/orch/alternative6-matching/SearchStochasticAlternative6MatchingNear.py --seed 14772914 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-alternative6-run-004
```

This snapshot was prepared before the previous local worker reached its cap. It uses the same single CPU search slot when launched.
