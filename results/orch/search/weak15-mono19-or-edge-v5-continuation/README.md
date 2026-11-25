Weak15 mono19 first-OR-edge V5 continuation: allocation failure

The process aborted with child exit -6 and std::bad_alloc after
422.228 wall seconds, before its authorized600-second bound.
The supervisor's own exit0 is not the search process's exit status; the child
status is explicit in run-metadata.json. CPU2, a hard1,000,000,000-byte address-space
limit and unchanged800MB estimated-memory guard were used. Peak RSS was
769,052KiB. The hard limit did not get raised or bypassed.

Last progress: 486,675 visits at
417.975 reported seconds. These are the
last reported counts, not an exact final census. No finished-case or circuit
verdict was produced. This failure is not UNSAT or a Lean proof.

The last atomically saved completed-only weak memo contains
76,286states, an increase of14,295
over the61,991-state input. Its full bytes are preserved and audited for context,
record shape, uniqueness and absence of all fifteen edge-OR root orbit images.
No stronger-mode cache was imported. Both memos have exact header:

    PNP_COPY_MEMO_V1 0 19 oredge 1

Input lineage points to the independently reviewed weak15 V3 continuation.
The source/binary are unchanged from that run. The fixed V5 matrix snapshot has
49 extras: the38-record V4 prefix plus11 independently audited symmetry cuts,
in addition to13 built-in matrices. Its exact SHA256 is
 e2c98359c0d903d5b439ec744de076267db30e674cb7e6d75d165337352e7f41.
Matrix/source audits are ../../review-weak15-new-symmetries.txt and
../../review-weak15-resource-guard.txt. The completed strong V3 case is separate.

Allocation failure prevented the final rectangle signal dictionary. The raw
rectangle stream also ends with an incomplete final record, retained exactly.
The audit parses and checks every preceding complete record, accepts malformed
JSON only at the final EOF, reports its exact byte length/hash, and explicitly
marks all unresolved signal IDs. Recorded cost sums are checked arithmetically;
this does not reconstruct every rectangle maximum or signature. All complete
bank histories are replayed on1024 truth rows. There is no complete recursion
proof DAG in these baseline traces. The initial strict-parser failure log is
preserved rather than discarded.

All available stdout/stderr, raw trace bytes, input/output memos, fixed matrices,
source, supervisor, lineage, audit and failure metadata are preserved. Four
streams are deterministically gzip-compressed with raw/packed sizes and hashes
in manifest.json. Decompress beside audit_outputs.py to replay its limited audit.
No automatic restart was attempted.
