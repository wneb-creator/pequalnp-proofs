# Archived auxiliary AND-count searches

Preserved after parent reported expired2590 lease. No solver remains active.

`search.py` models AND nodes whose operands/output are arbitrary ORs of inputs and earlier AND nodes. Empty ORs and unused nodes are allowed. It checks exactly the15 positive/15 maximal-negative rows, derived and verified independently against the graph, then exhaustively verifies all1024rows for SAT witnesses. Expanded binary circuits are also verified. This model counts AND nodes only; it does not enforce a total19gate limit. No native or Lean certificate is claimed for these SAT diagnostics.

Results:
- Six-AND star baseline: SAT, full1024validation, expanded23gates.
- Zero-AND impossible case: external solver UNSAT, sanity only.
- Unrestricted five-AND:60seconds UNKNOWN. Superseded by checked source L_meta_635, which already proves exact Petersen AND-count≥6.
- Fourteen-AND dual CNF baseline: SAT, full1024dual and primal validation.
- Unrestricted thirteen-AND dual: interrupted after circuit_search found an independently validated13OR Petersen circuit; UNKNOWN. The discovered23gate witness has10AND13OR and falsifies unconditionalOR≥14, not the posted total20 lowerbound.
- Missing-squarefree encoding positive sanity: the known ten-AND macro circuit is SAT with five missing edges, full1024validation. Six-star baseline with the same missing-edge requirement is UNSAT.
- No unrestricted six-AND/non-read1 search was started before lease loss.

For the missing-squarefree condition, a two-leaf proof through an AND macro must choose one bare input from each side; earlier AND outputs need at least two leaves already. An output edge has a squarefree proof exactly when an output-selected macro has its endpoints on opposite bare sides. The condition requires at least one edge without such a macro. It is disabled unless explicitly requested.

Complete CNFs, solver stdout/stderr, driver stdout/stderr, and result JSONs are preserved. `RUN-SUMMARY.json` records final statuses, and `MANIFEST.json` hashes all other archive files.
