# Final complementary retry of pair39

This checkpoint tests the branch in which frozen prefix aggregate wire30 has no readers. Every future selector referencing30 is forbidden; all primaries and every other nonoutput gate must have a reader. The prefix remains exactly the same17 fixed gates and the target budget remains24. Capacity constraints are deliberately omitted because their all-gates-read premise fails. Tail ordering and the reviewed compact blocking constraints are retained.

The26-gate positive control duplicates the aggregate computation in the variable tail and rewrites former wire30 uses to that duplicate; it passed SAT and full16,384-assignment validation. The target run was authorized only after independent source and assumption review, with at most180 solver seconds. Every SAT candidate is fully validated and any counterexamples are added.

Independent review established the case partition: earlier prefix gates already have fixed readers; every primary must be read because sampled singleton/edge assignments witness dependence; canonical tail pruning/padding preserves the fixed-prefix model. The normalized model therefore splits into aggregate-used and aggregate-unused branches. UNSAT in both this branch and ../final_retry_pair_39 excludes the original local case39, and only that restricted family. It is external SAT evidence, not a Lean certificate or an unrestricted lower bound.

Old archived counts and manifests remain unchanged. combined-status.json records whether the two reviewed branch results jointly settle the remaining family. Full stdout/stderr, exact commands, source hashes, samples, decoder schemas, metadata and results are preserved. CNFs are losslessly compressed; metadata records their original uncompressed SHA256 hashes.

Snapshot UTC: 2026-11-25T13:35:30.561497+00:00
State: UNSAT_UNUSED_AGGREGATE_BRANCH
Both branches UNSAT: True
