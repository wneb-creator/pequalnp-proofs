# Counterexample search for L-meta-1031

These are computational experiments, not Lean-checked proofs or refutations. No counterexample to the posted statement was found.

## Models

`counter_small.cpp` enumerates straight-line binary AND/OR circuits with distinct earlier operands, nonconstant gate functions, and no repeated wire function. The omitted constant, identity, duplicate, and forward-reference cases require normalization arguments before this can constitute a rigorous lower bound for the posted circuit model.

`counter_sat.py` uses Z3 bitvectors. It can synthesize any circuit, require a globally dirty AND, require a bad ownership profile, or require the posted nonempty star profile. It also supports a second OR output for extension-gadget searches. `counter_cnf_direct.py` is an independent one-hot encoding for CaDiCaL. Graph function equality is tested on all edge assignments and maximal independent sets. These are decisive for monotone circuits. Auxiliary-output searches use either the complete truth table (`subdivstar_full`: 128 rows), or a union of decisive tests for both outputs. The compressed auxiliary tests add each leaf singleton and the assignment true at every nonleaf to the graph edge/maximal-independent-set tests. These characterize the auxiliary OR because the circuit is monotone. The three-, four-, and five-arm inputs use 18, 29, and 48 rows respectively; the path7 and Y(1,2,3) inputs use 17 and 16 rows.

The solvers impose normalized syntax, used gates, and topological/commutative symmetry conditions. They are untrusted computations. `sat` witnesses are checked against the complete truth table by Python; `unsat` means only that the external solver reported UNSAT. `unknown` is a timeout and supplies no lower bound.

## Results so far

- Four vertices, depth four: 81,985 normalized prefixes, all 37 nonempty triangle/C4-free labeled graphs have a minimum found circuit with nonempty star ownership.
- Five vertices, depth five: 27,160,961 prefixes, all 290 nonempty labeled forests have such circuits. A second exhaustive pass found no dirty AND in any found minimum forest circuit.
- Five vertices, depth six: 1,460,469,821 prefixes; none of the 12 labeled five-cycle functions occurs. A seven-gate circuit was found and fully evaluated.
- C5 at seven gates: dirty-AND UNSAT (1.26 s), bad-profile UNSAT (4.09 s); SAT control witnesses have correct full truth tables.
- C6 and C5-with-leaf at eight gates: dirty-AND UNSAT (9.03 s / 11.32 s). Their optimum sizes were not established by these searches.
- Five-minute stochastic searches for Petersen at 19 gates and Fano incidence at 26 gates found no circuit. Counts: 3,559,004,844 and 3,372,699,873 circuit evaluations. Each best candidate missed one decisive test.
- General and fixed-AND-count Z3 searches for Petersen/Fano, variable eight-vertex graphs, and Theta(2,3,3) timed out UNKNOWN. See complete logs for exact variants and limits.
- A three-arm subdivided star with an additional OR of its three leaves: identity-padding queries exclude at most nine gates for both output orders (external UNSAT): 32.9 s with full rows and graph output last; 4.56 s with compressed rows and auxiliary output last. Direct Theta(2,3,3) and Theta(3,3,3) total-size queries timed out UNKNOWN.

## Useful witnesses

The C5 seven-gate SAT witness may have nested AND gates while remaining sound and having nonempty star ownership. Thus the stronger claim that every minimum circuit has only bottom-level AND gates is not supported.

The P4 five-gate bad-profile SAT witness is nonminimum and validates that the ownership encoding can detect bad profiles. This is not a counterexample to L-meta-1031.

All full text logs and search source files are retained here. Solver binaries and generated CNF files remain under the job scratch directory; they are omitted from git artifacts for size.

## Later count and gadget checks

The path7 and Y(1,2,3) tree gadgets with a far-apart three-vertex OR output also returned UNSAT at at most nine gates in both output orders. The four-arm subdivided-star gadget at thirteen gates timed out UNKNOWN in both orders.

`counter_count_only.py` collapses all uncharged gate cones: when counting ANDs, each charged AND takes two arbitrary subset-ORs of inputs and earlier AND outputs, and the output is a subset-OR. The OR-count model is dual. Constants and unused charged gates are allowed, so the charged count is an upper bound rather than an exact total-size bound. The toolchain/count agent independently reviewed this semantic reduction; the solver result itself remains untrusted.

External UNSAT results: C5 with at most two ANDs (0.01 s), C5 with at most three ORs (0.02 s), C8 with at most three ANDs (0.03 s), and Theta(2,3,3) with at most three ANDs (0.12 s). Positive controls C5/three ANDs, C5/four ORs, and C8/four ANDs all produced SAT witnesses that pass complete truth-table checks. Larger C8/Theta OR queries and Petersen/Fano count queries timed out UNKNOWN at 120 s.

The separate-count exhaustive census through six total gates found no violation of AND count at least the vertex-cover number or OR count at least the edge count minus one for any represented four-/five-vertex graph. This remains bounded computational evidence subject to the enumerator normalization caveat.

## Checkpoint status

Snapshot UTC: 2026-11-25T01:45:30.981013+00:00. Every log is a checkpoint snapshot of the complete stdout/stderr accumulated through that time. All currently launched search runs had finished when this snapshot was taken; UNKNOWN denotes timeout, not UNSAT. No counterexample to the posted statement was found.
