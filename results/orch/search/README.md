# L-meta-4970 counterexample searches

These are computational searches and positive controls, not Lean proofs of the posted statement. No counterexample has been found. A time-limited SAT run without a model does not establish UNSAT.

## Completed small exhaustive searches

The three C++ programs enumerate topologically ordered binary monotone AND/OR circuits, with exact truth tables, commutative operands, and structural T0. Duplicate wires with the same truth table, original-input OR-reach, and gate kind are omitted; deleting such a later duplicate and redirecting its references preserves the hypotheses and cannot increase either operation count. Targets are all nonempty C4-free bipartite graphs of the named sizes without an isolated-edge component. Such an edge cannot satisfy the posted star-witness hypothesis. Vertex-cover sizes are calculated by complete subset enumeration.

- `counterexample_small`: 1x2 through one gate (11 states), 2x2 through three gates (10,041 states), and 2x3 through four gates (1,490,485 states). No graph output below its claimed bound was encountered, even before checking star witnesses.
- `counterexample_2x4`: 136 target graphs, at most five gates, 399,653,516 states; no graph output below its bound.
- `counterexample_opcounts`: 35 target 2x3 graphs through five gates, 86,606,101 states; no violation of OR-count >= edge-count-1 or AND-count >= minimum vertex-cover size. The star-witness assumption is not required for this auxiliary test.

Compile a selected program with `g++ -O3 -std=c++17 <file.cpp> -o <output>` and redirect its complete stdout/stderr to a log. These bounded checks are not a general proof.

## Full-hypothesis SAT encoding

`sat_full.py` encodes a fixed-size binary backward circuit with an arbitrary selected output gate. Unused gates are allowed because the posted star witnesses need not feed the output. Subdivision K4 uses point vertices 0..3 and line vertices 4..9 for pairs 01,02,03,12,13,23. Fano uses point vertices 0..6 and line vertices 7..13, with incidence when the binary dot product of point+1 and line+1 is zero. These graphs have (edges, minimum cover) equal to (12,4) and (21,7), respectively; a counterexample would have at most 14 or 26 gates.

Gate semantics are encoded on every positive edge pair and every maximal independent negative assignment. These patterns determine the monotone output function exactly. Additional singleton and star-complement patterns determine pure OR witnesses: a monotone wire is OR_Q precisely when it is true on each singleton in Q and false on the assignment with exactly Q false. Every edge must have such an OR-gate witness on one of its adjacent stars with at least two leaves. Two structural reach flags exactly encode T0: AND resets both, OR unions them, and no OR may have both colours.

The decoder independently evaluates all 1,024 or 16,384 assignments, checks each pure-OR truth table, all edge witnesses, T0, C4-freeness, and the minimum vertex-cover size. The preserved 15-gate subdivision-K4 and 27-gate Fano controls pass these checks. They attain the claimed bound, so they are controls, not counterexamples.

`sat_full_symmetry.py` optionally orders adjacent independent gates by (operation, first operand, second operand), and restricts the first input pair to a representative under all verified colour-preserving graph automorphisms. A lexicographically minimal topological encoding satisfies both constraints: independent adjacent gates can be swapped and all later references and witnesses renumbered; graph automorphisms preserve the target and all witness requirements. It verifies 168 Fano automorphisms and covers all 105 unordered input pairs with six orbits. The Fano positive control satisfies both symmetry rules. `sat_full_order.py` is the earlier subdivision-K4-only adjacent-order variant.

Example reproduction, using Python 3 and CaDiCaL on PATH:

```sh
python3 results/orch/search/sat_full.py build Fano 26 /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26
python3 results/orch/search/sat_full_symmetry.py /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26
cadical -t 1800 /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26.sym.cnf > /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26.sym.solver.log 2>&1
python3 results/orch/search/sat_full.py verify /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26 /tmp/oec/pequalnp-pilot-157/sat_full_Fano_26.sym.solver.log
```

For the positive control use 27 gates with a separate prefix, then invoke the symmetry script with `--pin-control` and run CaDiCaL on its `.sym.pinned.cnf` output. For subdivision K4 use graph name `subK4` and 14 gates, or 15 gates for its control. The base script's `pin` command creates a canonical positive control without symmetry constraints.

## Randomized search

`anneal_graph_v5.cpp` is a star-aware random circuit search. It scores all positive-edge and maximal-independent-negative patterns, T0, and exact star-witness coverage using singleton/complement rows. For Fano this uses exactly 128 bit-parallel rows. It independently checks all assignments before printing FOUND. The target run uses 7 AND and 19 OR gates. It is heuristic and fixes the last gate as output; failure to find a circuit has no completeness meaning. Its 15/27-gate positive controls have zero errors and complete star coverage.

```sh
g++ -O3 -std=c++17 results/orch/search/anneal_graph_v5.cpp -o /tmp/oec/pequalnp-pilot-157/anneal_graph_v5
/tmp/oec/pequalnp-pilot-157/anneal_graph_v5 Fano 7 19 100000000000 8971 2700 1 > /tmp/oec/pequalnp-pilot-157/anneal_v5_Fano_total.log 2>&1
```

`MANIFEST.json` records SHA256 and size for each preserved artifact. Long search logs are copied after completion; a partial progress snapshot, if included later, is explicitly labeled as partial. The root agent holds the lease and handles all git/desk actions.

## Search stop at 2026-11-25 16:31:48 UTC

The root stopped both subdivision-K4 SAT runs and the Fano annealer after an HTTP410 lease response. All three exited 130 after SIGINT. Their complete logs are preserved here. Neither SAT run reached SAT or UNSAT. The annealer reached only the known near miss with one edge and its star witness absent. The prepared Fano26 SAT instances were never started. See `STOP-STATUS.json` for exact process status.
