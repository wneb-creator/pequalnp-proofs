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

The pruned-copy fixture audit checks14 indexed nodes, all fresh/disjoint closure alternatives, copied bases and152 bridges, and42 duplicate-preserving cofactor cuts. It also compares every generated Lean cut pool, choice and signal expression with the finite JSON. library_route independently reviewed the source and suggested the explicit selected-index bounds assertion that was added before the successful final rerun. These checks do not replace the pending recursive Lean exclusion theorem. The frozen script uses the original library_route and copy_checker scratch paths; the fixture/exporter are archived in search/pruned-copy and the checked cut source is archived in lemmas/PrunedCopyFixture0Cuts.lean.

The exact42-cut source-to-Lean mapping JSON is also preserved here as pruned-copy-fixture0-cut-map.json; restore it alongside the copied Lean source when rerunning that audit.

The concrete table audit and its full output, exact generator and selected row lists are also preserved. audit_pruned_copy_tables.py independently parses the generated Lean labels, masks, values and42 budget adapters against the fixture, then regenerates all uncovered gate alternatives. The generator uses only local finite data and emits the already preserved checked PrunedCopyFixture0Tables source. Its source/row JSON are reproducibility aids; compiling the frozen Lean module does not need Python. Restore the fixture,42-cut mapping, row-selection JSON and checked Lean sources at the scripts’ explicit original paths when rerunning.
