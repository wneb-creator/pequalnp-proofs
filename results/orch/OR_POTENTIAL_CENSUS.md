# Exploratory OR-budget census

This is an ordinary program search, not a Lean-checked proof. The candidate bound is `#OR >= |E| - rank_F2(four-cycle vectors) - 1`, truncated at zero. For a signal false on the empty input and every singleton, its pair graph has an edge exactly when that two-element input is accepted. Higher-order minterms are allowed.

## Why the projected search is a valid relaxation

Restriction of Boolean functions to the set of empty, singleton, and two-element inputs preserves AND, OR, false, and true pointwise. Thus every actual circuit maps to a circuit on these finite signatures with exactly the same operation sequence and OR count. A graph-function circuit maps to the signature of its graph. A general proper monotone function maps to the signature of its pair graph, irrespective of higher-order minterms. Consequently absence of a counterexample in the signature model implies absence in the original model; finding one still requires reconstructing and independently evaluating an actual circuit.

## Why AND saturation is exhaustive

AND gates have zero cost for this census. Initially all conjunctions of input signatures and constants are available. At each stage the available set S is closed under AND. Adding one OR value c creates exactly the new AND-closed set `S union {c AND s : s in S}`: products of multiple new factors reduce to this form because S was already closed. We enumerate every OR of two available values, deduplicate equal semantic states, and continue by OR count. A state denotes one jointly available collection of signals, rather than independently attainable functions. Constants are free, which is sound for an OR-only budget: true is an empty AND, and false can be read from an out-of-range wire.

The current Python implementation uses exact integer bit operations, exact finite-set exploration, and exact GF(2) elimination on four-cycle edge vectors. It does not use a numerical optimizer. Its current source and projection argument passed independent review; separate short reruns reproduced the smaller census counts. This supports an exhaustive computational conclusion in the stated model. It does not provide a Lean proof certificate.

## Completed checks

- All 64 graphs on four vertices pass through OR budget 2. This checks all proposed lower bounds on four vertices, whose maximum is 3.
- All 114 proper monotone functions on four vertices also pass the same check when represented by complete truth tables.
- All 1,024 pair-graph signatures on five vertices pass through OR budget 3: 624,170 transitions, 1.39 seconds. This includes arbitrary higher-order minterms through the restriction argument above.
- The full five-vertex budget-4 run completed: no counterexample, 40,230,740 transitions, 98.67 seconds. The maximum proposed lower bound is 5, so this covers every five-vertex case of the stronger pair-graph relaxation. This remains ordinary program evidence, not a Lean theorem.
