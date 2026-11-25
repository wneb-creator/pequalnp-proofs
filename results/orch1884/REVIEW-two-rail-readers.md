UTC: 2026-11-25T17:01:44.367436+00:00

Independent semantic review: PASS for TwoRailReaders.at_least_two.

The stable source is196lines/8281bytes with SHA256 ca8d293669aa925c7789d40980cc7e78359159f460a56ac84899de800b3322fe. Its archived validation reports check and export exit0; the complete archived streams were read (one nonblocking unused-simp warning, empty stderr). No new compilation was run.

The exact theorem assumes actual Petersen correctness on the eleven supplied wires x0,...,x9,not x0; FanInTwo; every NOT has at most one input; and both raw indices0 and10 occur in gate-input lists. It concludes at least two reader-gate occurrences of the rail set. This is a raw syntactic reader count, not a count of occurrences inside a gate or a general conclusion that both rails are used.

If at most one reader exists, UniqueReader isolates one list position. The two explicit use hypotheses force that same gate to contain both0 and10, while all other positions omit both. Fan-in two forces its operands to be exactly the complementary rails in either order. The explicit trimmed-NOT hypothesis rules out NOT at that position; AND/OR then has a constant value independent of x0. The fold invariant compares equal-length wire lists outside positions0/10, preserving the complement relation and agreement under every subsequent gate, including invalid references with the library default semantics. This argument establishes output independence of x0 when all rail-reading gates are coupled.

Correctness excludes output wire0 using the singleton0 row and output wire10 using the all-false row. The independent-set singleton1 and edge pair0,1 differ only in the two rails and have different target values, contradicting the preserved output agreement. No backward-reference or minimality hypothesis is silently used. Repeated equal gates are handled by list occurrence counting in UniqueReader; the conclusion is not inflated by two reads within one gate.

No forbidden root text, string literals, attributes, options, admitted proofs, native decision procedures or new axioms occur. The namespace is L_meta_1884 and the source is below512KiB. Imports remain local helper dependencies requiring inlining and a fresh standalone check for a final submission. This helper does not prove the full posted1884 statement.
