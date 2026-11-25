# Direct circuit minimization for L-meta-2962

These are heuristic search artifacts, not Lean proofs or exhaustive circuit
enumerations. The target graphs are the eight-vertex theta graph with nine
edges and the fourteen-vertex Fano incidence graph with twenty-one edges.
The searches try eleven and twenty-six AND/OR gates respectively, one below
their canonical graph-function constructions.

Phase 1 ran for 900 seconds and found no exact target circuit. Its best saved
circuits omit one edge and exactly compute the corresponding smaller graph.
They attain, but do not improve, the canonical bound for that smaller graph.
Candidate evaluation counts include repeats.

Phase 2 additionally searches for a strict improvement for any accepted-pair
subgraph of either target. It computes the exact minimum vertex-cover size by
bipartite matching and requires the active gate count to be strictly less than
the number of accepted pairs plus that cover size minus one. A passing circuit
must also compute the accepted-pair graph function on every assignment.
Independent source review checks the matching calculation, higher-degree-term
check and output-cone pruning. A discovered witness would still require
independent complete truth-table validation and a Lean proof.

The JSON summaries record completion status, exact counts and source hashes.
The complete logs preserve stdout and stderr. The independent review JSON files
describe controls and their limits. The source diff records the only phase-2
changes. `manifest.json` records archived file hashes and sizes.

To compile with a C++20 compiler:

```sh
g++ -std=c++20 -O3 -Wall -Wextra -o exact_minimize exact_minimize.cpp
g++ -std=c++20 -O3 -Wall -Wextra -o exact_minimize_subgraph exact_minimize_subgraph.cpp
```

Each executable takes the data filename, duration in seconds and an existing
output directory. Exit zero means a candidate was reported; exit one means the
time budget ended without a candidate. The data generator and positive-control
inputs are included. Successful positive-control recovery establishes that the
search and verification path can recover a known circuit; it says nothing about
the existence of a shorter target circuit.
