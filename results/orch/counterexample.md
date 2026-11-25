Counterexample strategy: L-meta-2592

2026-11-25 14:02 UTC: Circuit semantics audited. AND/OR/NOT only, fan-in at most two; invalid wire reads are false. NOT ignores its second operand. No loophole found.

No z3 CLI or Python package is installed, but system libz3.so.4 is available through Python ctypes. A CEGIS synthesis program is saved at /tmp/oec/pequalnp-pilot-103/counterexample/search.py. It chooses 19 gates using AND/OR/NOT/constant true, free invalid-wire false, requires some NOT, and initially requires all gates to be used. Thus UNSAT would only concern this search restriction; no formal lower-bound claim follows.

Each stage encodes gate truth tables as bit vectors over selected assignments. Initial examples include weight at most two, maximal independent sets, and weight at least nine. SAT candidates are checked over all 1024 assignments and counterexamples added. First running case fixes the first gate to AND on edge (0,1), with 240-second checks.

A concrete standard 20-gate monotone circuit follows from vertex cover (0,1,3,7,8,9). Assign stars:
0: 1,4,5; 1: 2,6; 3: 2,4,8; 7: 2,5,9; 8: 6,5; 9: 4,6.
Each star costs its degree in gates; joining the six star terms costs five ORs, totaling 20. This is an upper-bound baseline, not evidence for 19-gate impossibility.

All three reduction slots are already occupied: R_meta_2592_271, R_meta_2592_408, R_meta_2592_318. The desk reports reductions_live=3.

2026-11-25 14:11 UTC update: No19-gate witness. Generic broad searches (firstANDedge and firstNOTinput) and radius5localrepair produced no verdict before external termination; the Z3CAPI configtimeout did not reach the SMT command context. Fixed with explicit SMT :timeout. A oneNOT/firstORedge/distinct-function run timed out60seconds; radius3localrepair timed out120seconds. The SMT encoder was checked against a known21-gate circuit (20monotone plus unusedNOT), with every one of1024inputs verified.

Added QF_BV logic to select dedicated bit-vector solving. Added optional topology symmetry break: order gates by largest fan-in wire, then operation and smaller fan-in. A greedy topological order supports this representation; verified against the reordered21-gate reference. Added an optional maximumNOTcount2 restriction based on the lower-bound agent's proposed17binary-gate floor, pending Lean checking. No SAT/SMT result is a formal lower bound.

A short independent stochastic run reached weighted error18 (18false negatives,0false positives; unusedNOT) and was stopped to avoid duplicating circuit_search's ongoing stochastic route. Its missed minimal edge assignments were(0,5)and(3,8). Circuit_search now owns that route and shares candidates for SATlocalrepair.

2026-11-25 14:23 UTC update: Completed all 969 choices of three mutable gates around near19.json; every restricted neighborhood was UNSAT on the 82 initial examples. This is a local computational exclusion only. Total elapsed time was 168.55 seconds. Complete stdout/stderr for all cases is preserved in results/orch/search/neighborhood-details.json, with source and hashes alongside it. A broad 16-gate cofactor search with exactly one NOT has started, with a five-minute timeout.

2026-11-25 14:29 UTC update: The lower_bound agent reports its bound 17 + notCount C ≤ C.size is now Lean-checked. Thus the original 19-gate target needs only the one-NOT and two-NOT cases. The 16-gate cofactor search with exactly one NOT timed out after 300 seconds without a candidate. A second encoder now uses direct one-hot CNF and the Lean toolchain's bundled CaDiCaL. It passed both a positive reference test and a negative pinned-candidate test. Its global cofactor search started at 14:29:23 UTC, with a 300-second limit.

The circuit_search agent supplied twelve cofactor seeds: each has fifteen monotone gates computing the edge function with one edge removed, plus one unused NOT. The seeds are copied into the checkpoint as cofactor-seeds.json. The next local batch tests every triple consisting of the unused NOT and two other gates, for each seed (1,260 neighborhoods).

2026-11-25 14:37 UTC update: All 1,260 local cofactor neighborhoods were UNSAT. Each allowed changes to the initial unused NOT and two other gates in one of the twelve single-missing-edge seeds; the fixed initial examples already ruled them out. This excludes only those local neighborhoods. Complete diagnostics are saved in cofactor-neighborhood-details.json and the summary in cofactor-neighborhoods.log. No global circuit lower bound and no counterexample have been obtained by this search route.
