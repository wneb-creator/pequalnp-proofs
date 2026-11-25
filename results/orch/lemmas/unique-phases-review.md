# Independent unique-input soft-phase review

Reviewer: lower_bound. Date: 2026-11-25. Verdict: PASS for the optional phase artifact. The supplied network is not a target witness, and no new solver run was performed.

Reviewed `circuit-search/unique_input_phases.py`, its frozen `unique0-26-near.phases`, `unique0-26-near-seed.json`, and `unique0-26-near-report.json`, against `unique0-26-permissive-final.cnf/.map.json`, the original `near26.json`, and `sat-review/verified_symmetry.json`. All source/input/output hashes match the report.

The independent audit checked every supplied target automorphism and reproduced 168 mappings with raw input 0 occurring once. Exactly 144 also satisfy all 28 critical partner rows. The saved network is the exact lexicographically least topological normalization among those eligible candidates. Every predecessor reference is valid and sorted, output remains last, and the unique occurrence is preserved.

All 5928 phase literals are nonzero, unique, within the original 7253-variable range, and exactly match the reconstructed selector, operation, mux and output values. The remaining 1325 variables have no phase preference. The fixed CNF remains unchanged; the reviewed phase driver uses `solver.phase`, not assumptions or additional clauses.

All 16384 truth-table inputs independently confirm that the network computes exactly the Heawood graph with edge `(1,13)` removed. It has 47 false negatives and no false positives. Its single boundary mismatch is mask 8194, row index 5. The partial phase assignment satisfies 205934 clauses, leaves 2891 unresolved, and fully falsifies only `[7199]`, the target output unit for that missing edge. This expected conflict is harmless for soft preferences and is not a satisfying assignment.

- CNF SHA256: `86c036aaf5381cf4d574958b036eb8e32fa257d525fb2e4dd4fa2a33f4c86244`
- Phase SHA256: `5e96bcfb2eba5d129a8b4a0c3b899cb1e6d8d3bdbfba4698ff7cdb50768fa47c`
- Independent audit: `/tmp/oec/pequalnp-pilot-70/lower-bound/review_unique_phases.py`
- Complete exit-0 log: `/tmp/oec/pequalnp-pilot-70/lower-bound/unique-phases-independent-review.log`
