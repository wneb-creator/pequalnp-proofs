Search evidence for L-meta-2592

These files record computational searches, not Lean-checked lower bounds. No counterexample was found in the completed searches. The exact 20-gate upper circuit in `petersen_upper20.json` was evaluated on all 1,024 inputs by Python.

The CGP programs evaluate the complete Petersen truth table. Their `BEST` records include the 19 gate descriptions. For the NOT-constrained programs, scores initially include penalties for missing active NOT gates; a score below 128 has no such penalty. The first 20-minute unconstrained search ended after 4,065,730,000 mutations with four incorrect rows. Deduplicating its best candidate gives an 18-gate monotone overapproximation. The first 10-minute active-NOT search ended after 1,483,600,000 mutations with eight incorrect rows. A fresh search preserving exactly two NOT operations started after the lease renewal at 14:08:23 UTC; its output is written directly here.

The 21 SAT repair windows fix 13 gates and leave six gates free. They constrain all 1,024 input rows and require a NOT operation. CaDiCaL reported UNSAT for all of them. These are restricted repair problems; they do not exhaust arbitrary 19-gate circuits. The 20 indexed JSON manifests record their fixed unit clauses. The initial run's exact clauses were recovered from its original saved CNF, verified against the complete saved base CNF, and archived as `window-initial.json`. Complete solver stdout and stderr are retained. No UNSAT certificate from these runs has been checked in Lean.

The insertion searches add a NOT gate to the 18-gate near-circuit and modify one or two other gates. The two-gate version retains a beam of promising intermediate functions, so it is not exhaustive over all two-gate modifications. Neither search improved on four incorrect rows. Source hashes and counts are recorded in `counterexample-search-report.json`.

Gate operation codes in the C++ logs are 0 = AND, 1 = OR, 2 = NOT. In the SAT manifests they are 0 = AND, 1 = OR, 2 = constant true/padding, 3 = NOT. Input wires have indices 0 through 9. Subsequent wire indices are assigned in gate order. SAT manifests use the encoding from the repository's `notes/data/lrat-link/gennot.py` with n = 10, s = 19, A = 1055.

The first checkpoint was taken while the two-NOT log was live. Its candidate JSON is an independently evaluated earlier snapshot. The completed runs and final candidate files are identified below.

The later searches completed without a counterexample. The general two-NOT run ended with 18 incorrect rows; the adjacent and nonadjacent fixed-prefix runs ended with 22 and 22 incorrect rows. Their final candidates were independently reevaluated on all 1,024 inputs by `finalize_searches.py`. Final counts, hashes, and candidate paths are in `search-snapshot-2.json`; the earlier candidate JSON files remain historical snapshots.
