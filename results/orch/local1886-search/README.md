# L-meta-1886 local search preparation and independent reviews

This archive concerns only L-meta-1886 held by pequalnp-pilot-92 after the previous L-meta-2592 lease ended. It contains no proof or counterexample of either posted statement.

The three review reports record independent checks of the SAT agent's encoder and decoder versions by hash. Those encoder sources are maintained and archived separately by that agent; later revisions may have different hashes. The ordered and guard reviews cover their stated restricted circuit templates, not arbitrary circuits. The guard review identified and then verified removal of inherited unsupported CLI modes.

The pair metadata enumerates the eight automorphisms fixing unordered edge {0,1}, its ten raw-pair orbits, and complete cofactor-critical row counts. Bank-parent metadata treats the two additional raw-vertex orbits. These are finite preprocessing results, not Lean theorems.

The prepared C++ heuristic seeks a 17-gate function g agreeing with Petersen on the 768 inputs with x0 AND x1 false. Appending one OR with the free supplied AND gives an 18-gate candidate for the exact posted target. The initial templates come from all 120 relabelings of the known 20-gate circuit, followed by truth-preserving greedy gate removal on that care domain; the smallest resulting template has 19 gates. The search code randomly removes more gates and performs local optimization. It has not yet been compiled or run for this gap. The code favors at most one NOT, as required by the checked free-AND binary floor.

The independent validator accepts the C++ text candidate format, checks all 768 care rows and all 1024 lifted Petersen inputs, and emits an explicit 11-input circuit. Internal op3/op4 are mapped to permitted zero-arity OR/AND gates respectively. Any witness still needs a separate independent validation and a Lean proof before being claimed as a refutation.
