Signed18 first-AND-edge bounded search

The unchanged reviewed live_search_resume source was run from a fresh memo,
with signed mode, binary cap 18, first gate AND(x0,x1), a 300-second wall budget,
and a 5,000,000-node ceiling. No resume file was loaded. The supervisor pinned
one CPU, lowered scheduling priority, and imposed a 1,000,000,000-byte address
space limit. Peak resident memory was 210,432 KiB; the run exited 0 after 300.18
seconds and reported its ordinary time limit.

No circuit was found. The 446,597 visited nodes do not exhaust this case:
the root and four nested nodes remain open. Thus this is not UNSAT, a Lean
exclusion, or evidence that eighteen signed binary gates are impossible.
The question whether an eighteen-binary circuit can use at most one ordinary
NOT remains unresolved by this run.

The complete trace has 4,908 referenced truth signatures and records 249,859
cofactor leaves, 187,518 signed row leaves, 1,732 formula0 leaves, 3,570 formula1
leaves, 846 completed expansions, 3,067 memo links, and five open nodes.
The root visited 127 children; 126 terminated by row/cofactor checks and one
remains open. No claim is made about the unvisited successor count.

summarize_trace.py independently replayed every recorded binary operation
on all 1024 input assignments, every live-state transition, and every signed
row witness. It checked that memo references point to earlier completed
nodes with exactly the same remaining budget. It does not recheck cofactor
lower bounds/supply proofs, formula closures, memo automorphisms, or complete
successor coverage. These limits are explicit in trace-summary.json.

andedge-completed-resume.txt.gz contains only the 6,148 completed expand,
formula0, and formula1 nodes, never open nodes. Its header binds it to the
exact original trace SHA256. Any continuation must preserve signed mode,
the exact function pool and remaining-budget key, and the recorded trace
dependency. This cache was produced after the run and was not used by it.

check_witness.py can replay a found gate list and test phase realizations
of that fixed binary DAG with zero or one globally complemented wire.
Its independent twenty-gate monotone positive control and a transformed
twenty-one-binary/one-NOT control both match all 1024 rows. No candidate was
available in this run, so witness-result.json reports only that fact.

All stdout and stderr are retained without truncation. The trace and resume
file use deterministic gzip compression; manifest.json records original
and compressed hashes and sizes. The exact source is included. For a fresh
reproduction, compile live_search_resume.cpp using g++ -O3 -std=c++20, then run:

    ./live_search_resume --signed --cap 18 --first andedge --seconds 300 --nodes 5000000 --trace fresh-trace.jsonl

The source has no --help option. The recorded supervisor command and resource
settings are in run-metadata.json.
