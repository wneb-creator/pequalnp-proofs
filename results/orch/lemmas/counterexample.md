# L-meta-1768 sanity analysis

## Exact small cases, Python only

The independent script `counterexample.py` represents monotone functions by truth-table bitsets. It runs breadth-first search over sets of available Boolean functions, computing new binary AND/OR functions. Duplicate functions and equal operands are omitted: in a least circuit either can be replaced by an earlier wire, deleting a gate. State identification is sound for minimum gate count because future computations depend only on the set of functions already available.

For all nonempty graphs of girth at least five on at most four vertices, up to isomorphism, exact minimum gate counts are:

| Graph | Gates | Syntactic minimum circuits | Top-form minimum circuits |
|---|---:|---:|---:|
| One edge | 1 | 1 | 1 |
| Two-edge path | 2 | 1 | 1 |
| Two disjoint edges | 3 | 2 | 2 |
| Three-edge star | 3 | 3 | 3 |
| Three-edge path | 4 | 12 | 6 |

For the second pass the script enumerates syntactic circuits (unordered operand pairs) without merging states, so the counts preserve topology. Every listed minimum circuit has zero dirty AND gates. Therefore the selected pair set is empty in every top-form minimum circuit tested.

These computations are NOT Lean proofs. The script and full output are preserved for audit. This gives no evidence of a counterexample and does not establish the statement in larger cases.

## Structural observation

A target witness consists of a top a, an OR-input side vertex u, and an opposite OR-reachable junk gate g true on the pair input {u,v}. The semantic propagation through OR and the top's BelowF property imply:

- For every input x, if g(x) and x(u), then graphFun G x.
- Thus u belongs to TopForm.wmax G C g.

Consequently a possible reduction target is the union over junk gates g of graph edges uv where u belongs to wmax(g) and g({u,v}) is true. This drops topology restrictions and is stronger than the requested count, so it needs separate plausibility checking.

A further possible split is whether g is true on singleton v. The singleton case implies u is adjacent to every singleton accepted by g, and no-four-cycle limits common-neighbor sets. The genuine pair-minterm case may require following the earliest dirty AND gate that created the pair. Neither observation currently gives the required global linear charging bound.

## Requested 3-core reduction checks

The support bound passes the exact cases: edge 2≤2, path2 3≤3, matching2 4≤4, star3 4≤4, path3 4≤5. It has a generic mathematical proof: the binary output dependency cone has at most size+1 distinct input leaves, and each nonisolated graph vertex is essential. This does not require leastness. For an edgeless graph, support is empty; the zero-gate circuit can compute false by naming a missing output wire, so that case also satisfies the bound.

The generic peeling algorithm repeatedly deletes a positive-degree vertex of degree at most two. Exhaustive Python checking on all 32768 labeled simple graphs on six vertices verified that the surviving graph has degrees zero or at least three and that edges deleted ≤2 times the original support cardinality. This checks the reduction combinatorics independently of the circuit claim.

A nonempty girth-at-least-five 3-core must have at least ten vertices, by the degree-three breadth-first tree at one vertex. Therefore our exhaustive four-vertex circuit data tests only the peelable side. On the Petersen graph the core retains all fifteen edges; after deleting any one fixed edge the entire graph peels. This indicates a meaningful obstruction, rather than a new structural assumption falsely excluding the smallest cubic girth-five graph.
