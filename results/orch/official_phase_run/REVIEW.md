# Independent reviews preserved from the team record

The independent phase-generator reviewer was `lemma_search`. Its PASS verdict was delivered before the target run at frozen source SHA-256 `3d9b4edbe88a0e2c44b0dbed40a5a8abe4ff4077d12ce56624521a23dc85433c`. The reviewer independently replayed the actual CNFs and preference files:

- The exact 25-gate control assigned all 44,340 used variables, satisfied all 1,575,093 clauses, and computed the target on all 16,384 inputs.
- The approximate 24-gate seed assigned all 42,543 used variables. Of the 1,466,230 official clauses, only output clause 1169929 was false. All structural clauses were true. The normalized circuit preserved all 47 full-table mismatches of the original seed.
- Every selected operation/source was compared against the normalized seed JSON. Actual CNF hashes, complete assignment coverage, sparse variable indexing, operation mapping, adjacent independent-gate swaps, and preference-only output were checked. No blocker was found.

The independent wrapper reviewer was `counterexample`, reviewing the change authored by `toolchain`. The reviewed `cadical-phase-lrat.cpp` SHA-256 was `483193583107e3c94ce00515795aa35827f735a385d110f10f949f51d83815fe`. The review checked that tracing begins before DIMACS loading in the CONFIGURING state, that hints use `phase()` without assumptions or added clauses, that `conclude()` is valid for UNKNOWN as well as SAT/UNSAT, that traces are closed and incomplete outcomes identified, and that existing proof paths are refused. Tiny opposite-phase SAT, UNSAT, timeout, and overwrite controls passed.

The actual full-formula 25-gate wrapper control then returned SAT in 3.0127 seconds. The separate official decoder checked every one of its 1,575,093 clauses and all 16,384 inputs, with zero mismatches. The full wrapper sources, controls, and losslessly compressed complete 29.7 MB positive-control output are preserved under `../phase_lrat_tool/`.

These reviews establish the preparation and control results. They do not turn the target run's UNKNOWN result or incomplete trace into a lower-bound proof.
