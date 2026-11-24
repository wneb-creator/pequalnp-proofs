# Alternative6 balanced stochastic search

This is a distinct heuristic search for a 28-gate circuit for the exact 19-input, 24-edge Alternative6 core. Baseline29; a correct28 circuit would lift to the posted42-input function with96 further gates. No28witness is claimed here.

Fitness counts positive errors with weight1 and negative errors with fixed weight24/64. The archive admits weighted error at most12. A new warm-start hook merges two to four point stars into one biclique: every positive edge remains accepted, but new negative assignments are accepted too. These starts and saved overapproximations are explicitly INVALID. The physical saving is the sum of the selected point degrees minus the size of their neighbor union. Existing valid30/32/35 structured starts and legitimate redundant larger starts remain available.

The exact correctness flag, physical decoding, complete88 raw scalar verification, and Lean-verification requirement are unchanged. Improved positive-complete invalid circuits are recorded with all wrong raw assignments. No timeout or failed search implies a lower bound.

Author calibration on the final source:144full88 baselines,122valid and22INVALID, plus432physical mutants. Independent calibration:72full88 baselines,64valid and8INVALID. Full logs and author calibration source are included. Planned seed14772930,1200seconds, one local CPU after the prior run ends.
