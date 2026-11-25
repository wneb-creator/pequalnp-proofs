# Theta graph OR-budget search

This is exploratory evidence for a separate conjecture, not a proof or refutation of L-meta-3754. The graph has eight vertices and nine edges, formed by three paths of length three with common endpoints. It is bipartite and has no 4-cycle.

`or-budget-theta.py` encodes arbitrary monotone AND/OR circuits with a specified number of OR gates and unlimited AND gates. Each OR operand is a nonempty conjunction of raw inputs and earlier OR outputs; the final output is also such a conjunction. This flattens every AND-only region. The constraints use all nine minimal true edge inputs and all nine maximal false independent inputs, which characterize the complete monotone function. There are no star-witness assumptions.

The seven-OR query returned UNKNOWN after its 120-second solver timeout. The eight-OR control returned SAT; the emitted model was checked against all 256 assignments, and an independent reviewer checked both the encoding and that model. A timeout is not an UNSAT result.

`or-budget-theta-orbits.py` is a further exploratory query with first-OR edge-support symmetry reduction and an order on independent adjacent OR gates. It also returned UNKNOWN at seven OR gates after 120 seconds, while its eight-OR control returned SAT and passed the full truth-table check. This additional normal form has not received the same independent code review; no lower-bound conclusion uses it.

Reproduce with Python and Z3: `python3 or-budget-theta.py 7 120000` or `python3 or-budget-theta.py 8 20000`. The second argument is the solver timeout in milliseconds. All stdout and stderr are retained verbatim.
