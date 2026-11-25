Weak15 mono19 first-OR-edge V3 continuation

This is a bounded 600-second computational continuation of the independently
reviewed fresh weak15 benchmark in ../weak15-mono19-or-edge. It imports only
that run's 26,439 completed weak-mode states, whose full input memo is retained
here and whose exact SHA256 is recorded in lineage.json. No stronger-mode memo
was imported. The unchanged loader recanonicalizes input states. The memo
context is PNP_COPY_MEMO_V1 0 19 oredge 1; its final 1 denotes weak15 mode.
All 1,145 effective cofactor bounds equal their signed-table values.

The fixed, independently reviewed V3 matrix input contains 26 extra matrices
(six LP plus twenty symmetry records), in addition to thirteen built-in ones.
Its SHA256 is37e6f09e1de3891bd41d299717abff53f830f5d804b57659bad59478f1f3d1e5.
This exact snapshot was used throughout; V4 was not used.

Outcome: 876,417 new visited nodes in
605.013 reported search seconds and
608.827 wall seconds; process exit 0.
The completed weak memo now contains 61,991 states,
an increase of 35,552. Root present in completed
memo: False. Ordinary limit: True.
Finished-case verdicts: [].
This archive is computational evidence, not a Lean proof or an UNSAT claim
from a resource limit. The complete raw stdout/stderr and structured summary
supply the exact outcome.

The supervisor enforces one CPU, lower scheduling priority, and a
1,000,000,000-byte address-space limit; peak RSS was 775,196 KiB.
The source is byte-identical to the reviewed fresh weak15 source; its only
difference from the reviewed dynamic baseline is two memory stopping guards
lowered from1.5GB to800MB. Source review: ../../review-weak15-resource-guard.txt.
Input-archive review: ../../review-weak15-archive.txt.

All emitted rectangle and bank records, completed memo, input memo, source,
fixed matrix file, invocation/resource metadata, lineage and audit are retained.
These emitted traces are not a full recursion proof DAG. Future kernel replay
must export and validate proof dependencies; this memo alone cannot supply them.
The audit checks exact lineage hashes/context, profile bounds, trace arithmetic,
input-row polarity, every emitted bank history, and memo shape/uniqueness/root.
It does not recompute every rectangle maximum or reprove the cofactor bounds.

manifest.json records full raw and deterministic gzip sizes and SHA256 hashes.
Decompress the four gzip streams beside audit_outputs.py and run that script to
repeat the audit. run-metadata.json records the exact command and binary hash.
The source can be compiled with g++ -O3 -std=c++20 as in the preceding archive.
