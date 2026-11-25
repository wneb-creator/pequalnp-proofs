Signed17 first-OR-edge bounded search

This archive preserves the complete 300-second search trace, its exact source and log, and a candidate completed-state memo continuation. The first trace has an open root. Its linked continuation completes the computational first-OR-edge case with found=0. This is not yet a kernel-checked exclusion or the original theorem.

The trace contains302,957 node/done pairs,8,857 used truth signatures,171,298 cofactor leaves,124,038 explicit row leaves,1,302 formula0 and1,427 formula1 leaves,536 completed expansions,4,352 memo references, and four open nodes including the root. It contains no found witness.

Each node records its parent, remaining budget, current truth-function IDs and incoming operation/retention step. Each terminal records its reason. Cofactor masks refer to filtered projected-history gate indices. Signal records at the end supply exact truth tables. Formula leaves still require the corresponding finite closure certificates; complete successor coverage and memo automorphisms are independently regenerable. This is computational evidence, not a full kernel proof.

The resume file selects only completed expand/formula0/formula1 records, never open records, and binds them to the original trace SHA256. The continuation source emits explicit negative-ID memo references linked to those original node IDs. Its use must preserve and audit that dependency. It adds no new pruning rule.

manifest.json records both original and compressed sizes and SHA256 values. Gzip streams use a fixed timestamp. All original trace data are preserved.

The continuation loaded all3,265 completed computational exclusions and then exhausted all401 root children in15.0149 seconds, adding54,844 node visits. Its negative memo IDs refer to exact source nodes in the first trace; the resume header binds those dependencies to the first trace SHA256. Both complete traces and their truth dictionaries are retained. Exact options are in options.txt.
