# Alternative6 diverse stochastic search

Heuristic search for a 28-gate monotone circuit for the exact 19-input, 24-edge Alternative6 core. The standard baseline has 29 gates. A correct 28-gate witness would lift to the posted 42-input function with 96 further gates; the conditional Lean lift is already checked. No such witness is claimed here.

The source retains interleaved OR helpers, active-AND archive diversity, complete 88-test scalar witness validation, semantic reduction, and explicitly INVALID near-circuit recording. Warm starts include valid mixed clean covers at 30 gates, shared-sum two-dirty circuits at 32, and matching replacements at 35. Private right vertices are allowed in mixed covers; the exact physical cost and all assignments are checked. Sampling uses each selected vertex degree and mixed helper counts 1/2/4.

Author calibration checks 144 full-grid physical baselines on all 88 raw tests. Independent review checks 72 baselines on all 88 tests and 216 expanded physical mutants. Complete logs are included. Solver or heuristic failures establish no lower bound; any proposed witness still requires kernel-checked Lean verification.

Planned reproducible run: seed 14772923, 1200 seconds, one CPU, same local search slot. Complete stdout and stderr will be preserved separately when the run finishes.
