# Alternative6 mixed helpers with invalid near recording

This is the reviewed mixed OR/AND search for the exact19-input24-edge core, with a recording-only extension copied from the reviewed Triangle9Near model. Baseline29, target28, matching warm starts35. Helper cycles, objective, mutation and random choices are unchanged.

At most12 distinct near misses per1–4 errors and24 multi-dirty near misses with at most6 errors are preserved. They are explicitly INVALID repair seeds. Every record expands to physical gates, checks exact cost and topology, replays all88 complete extremal tests, and records every scalar wrong assignment. Valid witnesses retain full scalar checking and require Lean verification. No28-gate witness has been found by the calibration.

Independent source-delta review passed. The short author execution calibration and its separately scripted88-test artifact replay are preserved in full. Run: `python3 SearchStochasticAlternative6MixedNear.py --seed 14772918 --seconds 1200 --output-dir <scratch-directory>`.
