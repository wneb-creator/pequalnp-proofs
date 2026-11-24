# Complement12 balanced-negative heuristic search

This reviewed variant retains the exact33-input60-edge function,70-gate target,1962 complete search tests, and4156raw scalar verification cases from complement12-search/. Correctness and physical decoding are unchanged. No70gate witness is present.

To explore false-positive repairs, the heuristic negative-error weight is normalized by60/1902 and multiplied per restart by one of0.25,0.5,1,2,4. Positive errors have weight1. Archive admission uses positive-errors plus normalized negative-errors≤30, retaining the existing active-AND diversity key and10000entry cap.

Forty percent of baseline attempts try to combine two to four pure point stars into one biclique. These starts accept every positive edge but also reject too few negative cases, and are explicitly INVALID. The exact size is71 minus the sum of the selected point degrees plus the size of their neighbor union. The constructor verifies topology/cost and complete search signatures. Existing valid mixed72/shared74/matching77 and other redundant starts remain available.

A recording-only hook saves at most32 strictly improving positive-complete INVALID states of size≤70, with further improvements overwriting one latest file. Every saved state is physically replayed and scalar-checked on all4156raw cases, with exact mistaken assignments. The existing witness path still requires all4156 cases and subsequent Lean certification. The supplied70gate biclique fixture is INVALID, failing1508raw negative tests; it is a search seed only.

Author calibration checked96full4156 baselines (79valid,17INVALID) and288physical mutant expansions. Independent review checked48full4156 baselines (40valid,8INVALID) and144physical expansions. Both reviews and complete logs are preserved. This heuristic makes no lower-bound or existence claim.

Command: python3 SearchStochasticComplement12Balanced.py --seed <integer> --seconds 1200 --output-dir <scratch-directory>. Pass --seconds and1200 as separate shell arguments. The planned run replaces the current Complement12 worker at its cap; no extra persistent CPU is introduced.
