Fresh weak15 mono19 first-OR-edge benchmark

This was a fresh 300-second computational run with no memo input. Every one
of the 1,145 cofactor lower bounds equals its signed-table value: the ten
single-zero bounds were lowered from 16 to 15. The frozen reviewed V2 file
contains six LP matrices and seven symmetry variants, in addition to the
searcher's thirteen built-in matrices. The stronger-mode run and cache were
not touched or imported.

Outcome: ordinary limit after 300.55 reported search seconds, 301.22 total
wall seconds, exit 0. The run visited 734,033 nodes and 26,446 closures,
recorded 574,389 rectangle cuts, and preserved 26,439 completed weak-mode
memo states. No circuit or completed-case verdict was reported. The initial
root is absent from the completed memo. Two depth 7 copy branches closed;
the third was still active. This is not UNSAT or a Lean proof.

Peak resident memory was 771,372 KiB (753.3 MiB). The supervisor enforced
one CPU, lower scheduling priority, and a 1,000,000,000-byte address-space
limit. The only search-source changes, independently reviewed by the parent,
reduced two estimated-memory stopping guards from 1.5GB to 800MB. All other
source bytes match the reviewed dynamic loader. Fourteen projection-cache
resets occurred; the final estimate was 502,975,374 bytes.

All stdout/stderr, matrix input, source, guard-diff metadata, resource
metadata, emitted rectangle/bank traces and the completed memo are retained.
The traces contain all emitted records, not a complete recursion DAG.
The memo header is exactly:

    PNP_COPY_MEMO_V1 0 19 oredge 1

The final 1 marks the weak cofactor mode. Do not mix this cache with a
stronger-mode cache. A future kernel proof must export/replay its proof
dependencies; the memo by itself is only computational evidence.

audit_outputs.py checks the fixed matrix hash, all profile lower-bound
equalities, trace arithmetic and input-row polarity, all 164 emitted bank
histories, exact memo context, record shapes and uniqueness, and absence of
the root from the completed memo. It does not reprove each rectangle maximum,
all cofactor facts, every recursion transition, or the complete search.
output-audit.json states these limits explicitly.

V3, the final matrix set used in the completed strong run, was published
later and was not used here. Its reviewed SHA256 is
37e6f09e1de3891bd41d299717abff53f830f5d804b57659bad59478f1f3d1e5.
It has 26 extra records. A weak-only V3 continuation may be useful, but this
archive makes no claim that it closes or establishes the conditional
Petersen-lower20 premise needed to derive nine-variable monotone lower16.

The deterministic gzip files have complete raw/compressed size and hash
records in manifest.json. Decompress them beside audit_outputs.py to replay
the audit. Compile copy_search_weak15.cpp with g++ -O3 -std=c++20 to reproduce
the resource-limited search; exact arguments are in run-metadata.json.
