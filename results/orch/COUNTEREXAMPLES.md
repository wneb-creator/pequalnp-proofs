# Finite-case checks for L-meta-1031

These are exploratory computations, not Lean-checked theorems. The separate `lemmas/Counterexample.lean` contains a Lean-checked zero-gate base case for edgeless graphs and an explicit nonminimal C5 boundary example: an eight-gate circuit that violates star ownership, plus a seven-gate correct witness proving the eight-gate circuit is not least. It is not a refutation of L-meta-1031.

| Family | Checked instances | Outcome |
| --- | ---: | --- |
| Triangle/C4-free labeled graphs, 1 vertex | 1 | Minimum gate count equals star construction |
| Triangle/C4-free labeled graphs, 2 vertices | 2 | Minimum gate count equals star construction |
| Triangle/C4-free labeled graphs, 3 vertices | 7 | Minimum gate count equals star construction |
| Triangle/C4-free labeled graphs, 4 vertices | 38 | Minimum gate count equals star construction |
| Forests on 5 labeled vertices | 291 | Minimum gate count equals star construction; no minimum circuit has an unsafe AND |
| Cycle C5, 6 positive binary gates | 1 | HiGHS MILP reports infeasible, 45 seconds |
| Cycle C5, 7 positive binary gates | 1 | HiGHS finds a witness, checked on all 32 inputs |
| Cycle C6, 7 positive binary gates | 1 | Symmetry-reduced HiGHS model reports infeasible after 294.1 seconds; original model timed out300s |
| Cycle C5, 7 gates, at least one unsafe AND | 1 | Symmetry-reduced HiGHS model reports infeasible, 242.7 seconds; original model timed out300s and independent SAT timed out120s |
| Cycle C6, 8 gates, at least one unsafe AND | 1 | Original model timed out300s, no verdict |
| Cycle C5, 8 gates, at least one unsafe AND | 1 | Witness found7.4s and exhaustively validated; separate explicit8-gate witness checked in Lean |

The star construction uses `|E| + minimum_vertex_cover - 1` gates for a nonempty graph, and zero gates for an edgeless graph. For the four-vertex exhaustive BFS, truth functions are represented as bit vectors. Semantic state sets are explored by increasing gate count; every nontrivial AND/OR of two available functions is a successor. Constants, unary gates, and repeated functions can be eliminated from a minimum nonconstant circuit. No counterexample was found. Together with the cycle C5 solver result, these cover all303 labeled triangle/C4-free graphs on five vertices (291 forests plus12 cycles up to labeling), subject to solver trust. A flagged semantic BFS also exhausts whether a minimum circuit could contain an AND signal exceeding the target function. None does for all graphs with at most four vertices or for all 291 five-vertex forests. Flags are combined by existential union at equal semantic states; this is sufficient for the per-target unsafe-existence question.

The MILP model uses one-hot operand selectors, gate-operation bits and truth bits. It constrains the output to be true on every edge pair and false on every maximal independent set; monotonicity makes these test assignments sufficient for correctness on all inputs. All previous gates must be used later. The optional unsafe-AND constraint asks for an AND gate true on some maximal independent set. All returned witnesses are independently evaluated on the complete Boolean cube. Solver infeasibility is exploratory evidence only; no proof certificate has been checked in Lean.

C5 witness (inputs 0 through 4, new wires 5 through 11):

```
5 = and(0,4)
6 = or(2,4)
7 = and(3,6)
8 = or(0,2)
9 = and(1,8)
10 = or(5,9)
11 = or(7,10)
```

Sources: `lemmas/Counterexample.py`, `lemmas/CounterexampleBfsUnsafe.py`, `lemmas/CounterexampleMilp.py`, `lemmas/CounterexampleSat.py`. Complete diagnostics are saved under `/tmp/oec/pequalnp-pilot-54/` and will be copied into the branch results before delivery.
