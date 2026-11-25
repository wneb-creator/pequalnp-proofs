# Independent extra computational-evidence review

Verdict: PASS for preserving the exact 13 files listed below as external computational evidence. This does not establish L-meta-3451 in Lean. Later active CEGIS and nine-edge searches are outside this review.

The C8 case N=4, mask=43365, gate budget=10 returned UNSAT from CaDiCaL 2.1.2, exit 20, after 268.9565 seconds. The complete raw log and structured trial record agree. The compressed exact CNF independently decompresses to 3538497 bytes, SHA-256 9558abf6a9db0fe477b52ff1d670623f37fab3b1278bdb6d004aa3441d280e3c, with 12050 variables and 140285 clauses; all literal bounds and terminators match. The source hash identifies the previously reviewed ordered boundary CNF encoder. Alongside the independently replayed clean 11-gate witness, this supports computational minimum 11. No LRAT was generated for C8 and no kernel certification is claimed.

The new gate-kind count encoding differs from the reviewed ordered encoding only by nonoverflowing bounded counters and at-most constraints. For the actual calls, at most one kind is bounded: OR-copy padding preserves an AND bound, and AND-copy padding preserves an OR bound. Thus these calls cover at most the total gate budget. Calls bounding both kinds simultaneously would need a separate padding/completeness argument and are not certified by this review. For C6 mask=427 and total budget=10, the at-most-two-AND query returned UNSAT in 57.4294 seconds; the at-most-four-OR query returned UNKNOWN at 60 seconds. This is a bounded-size claim, not an unrestricted general AND lower bound.

The CEGIS encoder uses the same bounded selectors and reviewed simultaneous symmetries, begins with singleton and crosspair tests, and exhaustively evaluates each sampled model on all inputs. Positive edge tests preclude false negatives by monotonicity. It enlarges every false-positive independent assignment to a maximal negative and adds the resulting tests. UNSAT for any sampled relaxation excludes a full witness. Intermediate event=check/status=sat means only a sampled candidate; only event=full_validated_sat denotes a fully correct circuit. The smoke case N=3, cycle mask=371, budget=8 had eight false-positive inputs in its first candidate, added maximal negatives 7 and 56, then found a fully validated clean witness. Both candidate truth tables, error counts, and maximal-negative extensions were independently replayed. Intended cycle inputs have N>=3.

The selected scripts, metadata, and complete logs contain no credential access or live lease identifiers. Complete stderr files are empty. The prior 25-class census remains unchanged; this C8 result is an additional later outcome.

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/counterexample-extra-results.json | 969 | f591feebc29c04512c1c424aa39fca19ab68a65a76d901108dd0b9d617a2ef64 |
| results/orch/lemmas/counterexample_sat_counts.py | 6840 | c80d2000e811cb3a3ef5957927bcf7e25de0bb141bcb555801f29eec1523972b |
| results/orch/lemmas/counterexample_sat_counts_batch.py | 318 | 461581d21c3ca5def604935e1be7432ce7936f3b942192721a923c14c6f6fa4c |
| results/orch/lemmas/counterexample_sat_counts.stdout | 2818 | fc92be6cfadff72130d6a1af841e5faf8ddd74694ad99eae949de2210c59b78f |
| results/orch/lemmas/counterexample_sat_counts.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_cegis.py | 6167 | f70ea3a7f90f5224de37cbd039a43075677e4cd6a29581883ac2b891e0635111 |
| results/orch/lemmas/counterexample_cegis_smoke.stdout | 2678 | 446982d74e1b499e7c5cd639bda55060b0dce71c6ddfcc3e7ed46c817e0f9b17 |
| results/orch/lemmas/counterexample_cegis_smoke.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-1200-trial.stdout | 835 | 951e52879383196ac643764c7ef6d91a9f3158a70c0702dd91dd6ab3e022ed26 |
| results/orch/lemmas/c8-ten-1200-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-1200-cadical.stdout | 45453 | 32d628c48c6364f09b8c56a16503d6ec78d4f5e1269104a8d7a286079dadc9f0 |
| results/orch/lemmas/c8-ten-1200-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/certificates/c8-ten.cnf.xz | 342840 | 11d94a07d5ca0bc43b789d8cb09961a16a9011221b408ed56bbf07584a4e25bb |

Reviewer: status_review. No proof or solver source was modified.
