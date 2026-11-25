# Unknown C4-free bipartite graph control

This is a computational search over graphs on two fixed sets of four vertices. All four diagonal edges are required, so the graph has vertex-cover number exactly four. Every complete two-by-two bipartite subgraph is forbidden. The graph itself is an unknown part of the SAT instance.

The circuit model has three AND gates. Each operand is a nonempty OR of any original inputs and earlier AND outputs; the final output is a nonempty OR of selected AND outputs. Operand regions may overlap. There are no source-disjointness, connectivity, sorting, gate-use or first-gate symmetry restrictions. All 256 input assignments equate the circuit output with the unknown graph's edge-disjunction function. This is an AND-count test with unrestricted OR-region size, not a total-gate or derivative test.

CaDiCaL reported UNSAT in 5.21 seconds for this model (5193 variables, 21295 clauses). A positive control fixes the graph to the diagonal matching and allows four AND gates: SAT in 0.096 seconds. The decoded control satisfies every CNF clause and independently evaluates correctly on all 256 masks. The control may reuse earlier AND outputs inside its OR regions; its explicit netlist is preserved in the JSON.

This is not a Lean theorem. No general arbitrary-circuit normalization theorem or formal CNF bridge has been established here. It does not prove the 13-AND plane bound, any total-gate lower bound, or L-meta-2602. Full solver stdout and stderr are preserved in gzip. The CNFs are deterministic from the source and their hashes are recorded rather than storing duplicate formulas.

Run the source from the job environment with `3 --seconds 30`, or `4 --seconds 10 --control`. It uses the fixed job scratch directory and the pinned Lean distribution's CaDiCaL. The standalone validator regenerates both CNFs, checks archived hashes and the positive witness, and performs all 256 scalar evaluations without rerunning the solver.
