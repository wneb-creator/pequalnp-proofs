Independent trace audits for the signed17 OR-edge and OR-nonedge experiments.

The three Python sources are preserved byte-for-byte after independent review by
library_route. They perform finite replay checks and do not launch search or
solver jobs. Complete stdout results are preserved alongside them.

These are exact frozen sources from the original container. Their BASE paths
refer to /tmp/oec/pequalnp-pilot-87/library_route, and the part2 audit also reads
the archived resume gzip under /workspace/pequalnp-proofs/results/orch/search.
To rerun elsewhere, adjust these explicit local paths or reconstruct the
original scratch layout using the reviewed live_search.py and the three raw
trace/resume files from search/signed17-or-edge/*.gz. No credentials or network
access are used. The trace raw hashes are checked/reported by the audits.

The audits validate transitions, row witnesses, projected replay masks, memo
isomorphisms and complete successor sets. They do not certify formula leaves
or supply their transported cofactor lower bounds in the Lean kernel.

The OR-nonedge source differs from the reviewed part2 source only in its trace filename, expected first-case label and second initial operand (x2). library_route independently reviewed these three substitutions. Its complete output records the440569-node replay; the raw input is preserved in sibling search/signed17-or-nonedge.
