# Independent final computational-evidence review

Verdict: PASS for preservation of the frozen final evidence. No result here proves or refutes the posted L-meta-3451 statement. All eighteen manifest files were independently rehashed and matched their declared lengths: total2703378bytes. Manifest SHA-256 b6eaf81d98dc50e8178f0c257f22c01609cc7d9f6d988817001c4668bd9b2e9c.

## Final verdict accounting

The colored K4 lift exact search at budget22 reached its900-second limit. Both raw CaDiCaL and structured trial logs report exit0/UNKNOWN, with elapsed900.0608seconds. The C8 singleton-dirty query at its known optimum11 returned UNKNOWN after300.0330seconds. Neither is UNSAT, a lower bound, or a counterexample. The updated README correctly distinguishes this stronger every-minimum-clean query from the posted existence claim.

The300-second colored heuristic recorded86142256 mutations and14358 restarts, with no full_validated_sat event. Its preserved22-gate candidate has one wrong boundary assignment and68 full-input errors. Independent replay shows all68 errors are false negatives, with no false positives; boundary input130 (point1 and line0) is rejected incorrectly. Its ANDs are clean, but it computes the wrong function and is not a witness. The smoke run has the same candidate and correctly reports a heuristic nonfinding.

## Independent replay and encoding scope

Independently reconstructed all93 boundary assignments and all45 logged one-gate-deletion seeds from the reviewed23-gate fixture. Replayed every seed on all16384 assignments; all recorded error counts agree, ranging from68 to4558, so no exact initial seed was missed by the heuristic logging convention. The best-candidate JSON exactly matches the final log record. Full errors, boundary errors, and AND cleanliness were independently recomputed for every recorded improvement. The heuristic source hash and fixture hash match both logs.

The exact wrapper only substitutes the previously reviewed24 incidence-preserving K4 automorphisms into the unchanged encoder. The source preserves earlier-wire bounds and only records a full heuristic witness after exhaustive truth-table validation; no completeness inference is made from heuristic failure. The N5 CEGIS paragraph retains the prior stopped-run distinction and explicitly attributes the cycle theorem to source inspection without a transitive axiom audit or formal bridge. The known clean23-gate colored-lift upper bound remains valid; no smaller valid circuit was found.

## CNF integrity and public scope

The colored CNF xz independently decompresses to31747983bytes with SHA-256 a7d11907cc67040817b601974558dffb4d04b4a64d749b9ac412154182b75283. Streaming validation confirms the DIMACS header76309variables/1019676clauses, all literal bounds and clause terminators, and the recorded complete raw hash. Compressed size/hash and every nested final-metadata file record match the frozen bytes. This verifies integrity and syntax, not a formal CNF-to-Lean bridge; there is no UNSAT certificate for this unresolved run.

All selected public text and source files contain no credential access or live lease identifiers. Complete stderr logs are empty. The final README and metadata accurately label UNKNOWN, interrupted, rejected sampled candidates, and heuristic nonfindings, and do not claim a full Lean theorem.

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/certificates/colored-k4-twentytwo.cnf.xz | 2617552 | d6b57c028fdcae611bc408aaa7303db4a2b3ee3a8097bf91616fa1acd9d3a2e8 |
| results/orch/lemmas/colored-k4-twentytwo-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/colored-k4-twentytwo-cadical.stdout | 32951 | b9e85b6a9e8e7e78e20b9a77abe237f633cfcf073be4bf3ed254879578d90d6e |
| results/orch/lemmas/colored-k4-twentytwo-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/colored-k4-twentytwo-trial.stdout | 2884 | 116a597224b155129039a714cd285deac5b082e45ff337b515fdc096f48c4abd |
| results/orch/lemmas/counterexample-README.md | 6561 | 377d0ad35dd452b1581be7927ab7e63864498532fa482fff5a765c44030cd9de |
| results/orch/lemmas/counterexample_c8_dirty_optimum.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_c8_dirty_optimum.stdout | 1416 | 1da067929eec0449f7625cdcec5b2ee5e5ec936fa926cae9e474ba0cfa38e8a2 |
| results/orch/lemmas/counterexample_colored_final.json | 2563 | 90ec0e7d1c7a91482d1bb02e9f1c067620d5b5a1441478ec2ee4d96db9a56388 |
| results/orch/lemmas/counterexample_colored_heuristic.py | 5505 | d3ba3b44518c7b628ae0b8e8d84ff56aaab692a3aeb17a233e1647a510a4f8c8 |
| results/orch/lemmas/counterexample_colored_heuristic.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_colored_heuristic.stdout | 13810 | 6be9604c8b7dde061bec3c73b8a63dad6a89b33464e00ce2a82b155e18fc29da |
| results/orch/lemmas/counterexample_colored_heuristic_best.json | 1223 | 1e9b103722d323b7c825cc3ccea86a86e047ef6b225e485aa4c29914c8e59852 |
| results/orch/lemmas/counterexample_colored_heuristic_seed_validation.json | 671 | 216e90f84e26390bf69e0cf233bcd0383a760a5c334f798aca336776a83fad00 |
| results/orch/lemmas/counterexample_colored_heuristic_smoke.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_colored_heuristic_smoke.stdout | 13803 | 3896c8165c8c2a94846b31ac17a9610d4eb6d9936706a801aea21ab5de260a9a |
| results/orch/lemmas/counterexample_colored_lift.json | 2072 | fa550749a3e9e43c1fec0dbe7a12fbd033d39f07bdbfb68269d91a955fc9640f |
| results/orch/lemmas/counterexample_colored_trial.py | 2367 | ccd6d146e4fa4265f7cf4d6c78cbf697740cd173ab360c52d8e588d94916df16 |

Reviewer: status_review. No main Lean, solver, fixture, or result source was modified.
