# Independent joint TEN phase review

Reviewer: lower_bound. Date: 2026-11-25. Verdict: PASS for the frozen branch-3 soft phase artifact. This is not a target witness, SAT result, or UNSAT result.

Reviewed source: `/tmp/oec/pequalnp-pilot-70/constructive/joint_phases.py`, including its `joint_smoke.normalize` and `joint_decode.evaluate` helpers. Reviewed driver: `/tmp/oec/pequalnp-pilot-70/circuit-search/phased.cpp` and the installed CaDiCaL header's `phase` contract. The driver sets default decision phases using `solver.phase`; it adds no clauses or assumptions from the phase file. The production wrapper is reviewed separately by circuit_search.

Frozen inputs are `joint-ten10.map.json`, `joint-ten10.cnf`, and `four-star-cut-cone-seed10-missing-1-13.json` in constructive scratch. All recorded input hashes match. The phase file has exactly 991 nonzero, unique, in-range literals among 1423 variables; 432 auxiliary variables have no preference. I independently reconstructed every literal from branch 3, its signed cut cells, normalized gate selectors and operations, and all gate input/output row values. There are no contradictory preferences.

The raw and normalized seed networks agree on all 1024 residual assignments. Both compute the residual graph with local edge `(0,9)`, corresponding to original edge `(1,13)`, removed. The one boundary mismatch is mask 513; the complete residual target mismatch count is 16. Independent fixed-cut embedding checks and all 16384 full-input evaluations show that the 26-gate embedded network computes exactly Heawood with edge `(1,13)` removed. Its full-target mismatch count is 47. It therefore remains a near-seed, not a solution.

Of the 24789 frozen CNF clauses, exactly one fully assigned clause is false under the supplied phases: `[1411]`, the output requirement at boundary mask 513. This is compatible with soft phase preferences and is not an assertion that the partial phase assignment extends to a model.

- CNF SHA256: `80fcc7fd598276ab66375282674e77f777dfc623e388f2d36ff5e48aa3cacb4d`
- Phase SHA256: `a7a406cf3e3132ccede311d2e417667e5079c888e67854e42816a7a2cf69200c`
- Independent audit: `/tmp/oec/pequalnp-pilot-70/lower-bound/review_joint_phases.py`
- Complete log: `/tmp/oec/pequalnp-pilot-70/lower-bound/joint-phases-independent-review.log`

The independent audit exited 0. No solver run or Lean build was started for this review, and no production artifact was modified.
