# Alternative6 with interleaved mixed OR helpers

This model extends the prior alternative6 search to share OR subexpressions that can contain previous AND outputs. It adapts the independently reviewed triangle9 mixed model to the19-input24-edge alternative6 function. The six point-star starts use degree-aware sampling. Helper cycles are1/2/3/4 AND rows,1/2/4 linear OR rows and1/2/4 interleaved mixed OR rows; these bounds fit the six-star initializer. Interacting two-dirty matching warm starts have35 gates. Target28, standard baseline29.

Valid structural candidates of size<=31 pass through the complete-test signature reducer. Any saved reduced witness or dirty29 warm start is independently scalar-checked on all24positive+64negative extremal inputs. Only a Lean-checked target witness would count as a refutation. No28-gate witness has been found.

Author calibration checked720 baseline/mutant expansions for physical gate count, topology and scalar88-test semantics; independent review checked60 valid baselines with mixed helpers. Sources, exact problem data and full logs are frozen here. Search objectives, mutation, decoder and reducer are inherited from the reviewed triangle9 model; only dimensions, degree-aware initializer and target thresholds changed.

Planned command from repository root:
```
python3 results/orch/alternative6-mixed/SearchStochasticAlternative6Mixed.py --seed 14772917 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-alternative6-run-005
```

This uses the same local search CPU slot after run004 finishes. The finite graph proof route continues independently.
