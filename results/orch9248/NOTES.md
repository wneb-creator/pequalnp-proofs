
## 2026-11-25T17:08:33.881240+00:00 — status_check initial scope audit

The new own lease is L-meta-9248, assigned17:07:31UTC. Exact posted goal denies a RUP learned-clause list of length at most12 containing the empty clause for PHP(5,4). The run is newest-first, and each learned clause is RUP over the original input plus all older learned clauses; input clauses are free and never consume run length. PHP has five positive four-literal pigeon clauses and40 negative collision clauses; it imposes no at-most-one-hole condition on a single pigeon. UPForces is inductive finite unit propagation, not coinductive/self-supporting. Learned clauses are arbitrary literal finsets, potentially tautological, and no width restriction occurs. Root owns lease/git; this agent audits definitions, checked related sources and later diffs.

## 2026-11-25T17:10:40.712019+00:00 — status_check checked-source results

Seven working-tree files mention IsRUPRun. L9250 gives an actual20-clause PHP5,4 run (c0 throughc19), despite its posted≤24 conclusion; L9466 duplicates that construction for≤53. L9237 excludes≤6 for the exactPHP5,4 instance. L9198 andL9208 exclude≤3 and≤4 respectively forPHP4,3. L9469 is a62-state partial-assignment adversary excludingPHP6,5≤10. L9477 supplies a compact generic replay/verify soundness proof and an actual50-stepPHP6,5 run. No checked≤12/13 exactPHP5,4 result was found. Full-history subject9247 is an unrelatedRepSizeAtMost proof, not the RUP opposite row; exact9248 proof not found.

The new RUPHarness is independently reviewedPASS, exactSHA8f5f89f7f1abd53fd77eef5c439a8e68780c9308c58a6381ce0542a8529e1cee. Generic replay throughverify_sound byte-identical to acceptedL9477; current valid fixture has5row+40collision clauses and the single-row smoke run is not a refutation. This supports kernel-checking any later concrete trace but does not resolve the posted lower bound.
