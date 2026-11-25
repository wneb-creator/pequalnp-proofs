# Finite-case investigation for L-meta-2448

These are computational investigations, not Lean-checked results; exhaustive cases and heuristic searches are distinguished below.

- For 4 inputs, enumerated semantic AND/OR circuit states through depth 4. All 38 labelled triangle-free, four-cycle-free graphs had a minimum witness with a star profile. State counts by depth: 13, 126, 1102, 9279.
- For 5 inputs, enumerated through depth 5. All 291 labelled forests had a minimum witness with a star profile. State counts: 21, 330, 4750, 67005, 958669.
- The remaining 12 labelled admissible 5-vertex graphs are copies of C5. Every possible extra AND/OR gate from every depth-5 state was checked; none computes a C5 edge function. Thus the computation finds no C5 circuit with at most 6 gates. Standard star-cover circuits have 7 gates.
- A separate scan of every minimum output candidate arising from the chosen canonical state witnesses found no minimum circuit lacking a star profile. This is not exhaustive over ownership profiles, because equal semantic signal sets share one circuit representative.

Method: represent each signal by its full truth table, start with all input signals, and enumerate every new binary AND/OR of available signals plus a nullary AND for true. Constant false is freely available from an out-of-range wire, but gates involving it cannot produce a new useful signal. Duplicate semantic gates and unary gates cannot improve a minimum. State keys are sets of generated truth tables; each state stores one circuit witness. This merging preserves reachability/minimum gate counts, not ownership profiles. The star check uses each gate's ancestor set and tests the literal Owns condition at each graph edge.

Structural obstruction: ownership is not automatically star for arbitrary computing circuits (an irrelevant nullary AND owns every edge). In a minimum circuit, constants, unary aliases, and dead gates should disappear. An AND owning two disjoint edges has a false positive on a singleton/nonedge among the four endpoints, as already proved inside R_meta_2448_263; the unsolved exchange must remove/move such an AND without increasing size. This finite search found no counterexample.

Original scratch copies are under /tmp/oec/pequalnp-pilot-75/finite/; reviewed artifacts are also preserved in results/orch/finite/.

search.py SHA256 a621076064c49e96f7a929fc27c799f7fafe086042defeeeaedf490345ececde

search5.py SHA256 bde2d8cf88f63496dde605b9e66f9cbcaf67970786355fbef4ae720f8d85db11

search5six.py SHA256 5496fef9b054e8417f9c8a84a93417cd7e3e8965dfee0d70617289802368f06d

nonstar5.py SHA256 232b4b122949d162eca06d834828cae5b02206adac0944e3021c867f1d7e52ac

Updated 2026-11-25T07:08:47.241942+00:00

## Larger and profile-directed heuristic searches

The local environment has g++/scipy/numpy but no z3/pysat/ortools. A C++ circuit search uses an exact test reduction for monotone circuits: every graph edge pair must be true, and every maximal independent set must be false. Monotonicity then determines every other assignment. Petersen has 30 critical rows (15+15); Heawood has 58 (21+37), so every signal uses one uint64. Minimum-cover star circuits seed the search; removing one gate supplies near-correct candidates. Target sizes: Petersen19 versus cover20, Heawood26 versus cover27. Both 600-second runs remain in progress as of this note. No exact candidate has been found yet.

Independent profile-directed annealing at the cover size searched for a computing circuit with an AND owning disjoint edges. No such circuit was found for C5 (7 gates, 513.8 million mutations), C6 (8 gates, 877.4 million mutations), or C5+leaf (8 gates, 613.0 million mutations), 120 seconds each. These are heuristic negative observations, not lower bounds or proofs that all minima have star profiles.

A random 7-input DAG census is also running: whenever a generated signal is exactly a pure graph edge function, derive its graph, reject triangles/4-cycles, and compare the useful ancestor cone size with the graph cover bound. A below-bound circuit or an equal-bound circuit with bad ownership will be reported for inspection.

Updated 2026-11-25T07:17:45.210352+00:00

## Completed heuristic results and preserved artifacts

- Petersen,19 gates:4,332,400,000 mutations,21,662 restarts,600.004s; best one failed critical row, no exact witness.
- Heawood,26 gates:3,947,000,000 mutations,19,735 restarts,600.010s; best one failed critical row, no exact witness.
- Random7 census:82,736,023 DAGs,1,043,016,003 generated signals,337,678,872 exact quadratic graph outputs,327,356,158 admissible outputs,297,678,746 useful output cones at or below their cover bound,23,621 distinct admissible graphs encountered;180.001s; no below-bound or bad-profile at-bound witness. This is randomized coverage, not exhaustive over all circuits.
- Shared-pure-OR census:26,966,436 DAGs,339,934,059 signals,110,043,677 quadratic outputs,106,680,756 admissible outputs,97,007,076 at/below-cover useful cones,18,700 distinct admissible graphs;60.002s; no shared pure OR witness. Sharing means two distinct parent gates in the useful output cone, and pure OR is checked on the complete128-entry truth table.
- Canonical BFS minimum-witness scan on all291 five-vertex forests found no shared pure OR signal with at least two singleton supports. Alternate implementations of equal semantic states were not exhausted.

Programs, exact graph files, critical-row files, completed full logs, and a SHA256 manifest are preserved in results/orch/finite/. Sources can be compiled with g++ -O3 -std=c++20; no third-party solver download was used.

Theta targets now running: theta(2,3,3) has vertices0..6 and edges02,03,05,12,14,16,34,56; alpha3, cover number4, cover circuit11, search10. Its exact critical rows are5,9,33,6,18,66,24,96,3,42,44,52,76,81,84. Theta(3,3,3) has vertices0..7 and edges02,04,06,13,15,17,23,45,67; alpha4, cover number4, cover circuit12, search11. Its rows are5,17,65,10,34,130,12,48,192,3,86,88,100,104,148,152,164,169. Each is receiving600s of heuristic search.

A distinct bounded MILP synthesis model is also running on each theta target for300s with HiGHS threads=1. Gate operations, fanin selectors, and all critical-row wire values are binary variables; last-wire outputs are fixed to the graph truth values. The model was validated with a fixed C5 seven-gate cover circuit and its returned circuit independently rechecked on all32 assignments (no failures). Source run1 is preserved because SciPy ignored parallel='off'; threads=1 was accepted. Future source uses parallel=False. A timeout will be reported only as a timeout; numerical solver infeasibility would still not be a Lean proof.

Updated 2026-11-25T07:25:46.035318+00:00
