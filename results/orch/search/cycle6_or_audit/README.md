# Six-cycle OR-count audit

This search concerns the six-cycle edge function on inputs 0 through 5: an assignment is true exactly when two cyclically adjacent inputs are true. Each OR node has two operands, each an arbitrary nonempty conjunction of inputs and earlier OR-node outputs. The final output is another nonempty conjunction. The number of AND operations is unrestricted in this representation.

All 64 assignments are encoded. CaDiCaL returned UNSAT for four OR nodes in 0.81 seconds, then SAT for five OR nodes in 0.088 seconds. The five-OR witness was independently evaluated on all 64 assignments. These are computational results: neither the encoding nor a normalization theorem from general AND/OR circuits to this representation has been proved in Lean. This is not a result for L-meta-2602.

The original scripts, full solver stdout/stderr, summaries and independent validation are preserved here. Gzip files retain every original byte. `manifest.json` identifies the exact encoder, imported dependencies, solver, arguments and CNF hashes. The CNFs are reproducible and omitted. The scripts preserve their original job-local paths; their `CNF` helper is in the parent search directory.

The five-OR control is independently rechecked by `validate.py`. UNSAT is not inferred from a timeout or from the separate stochastic C6 search.
