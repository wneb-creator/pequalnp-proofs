# Restricted union-DAG census

This is a small exhaustive Python computation, not a Lean proof. It supplies
pruning conditions for the restricted pure-union multi-output search. It does
not prove a 39-OR lower bound and does not exhibit a counterexample to the gap.

`union-dag-census.py` reads the existing immutable
`multi-output-line-neighborhoods.json`. Its complete stdout and stderr are
`union-dag-census.json` and `union-dag-census.stderr.txt`.
The output records the input hash and enumerates every 13-bit union and the
minimum transversals for all 13 outputs.

There are 1,638 requirements `(p,D)`. A union `U` covers one when it contains
the four-line pencil `N(p)` and is disjoint from the generic negative cap `D`.
Exactly 157 masks have no disjoint negative cap whatsoever. Such a mask and
every union containing it cover no requirement, so these masks are safe to
exclude from a useful pure-union DAG.

The coverage is constant for each listed pair (union size, contained pencils):

| Size | Pencils | Covered requirements |
| --- | --- | --- |
| 4 | 1 | 126 |
| 5 | 1 | 78 |
| 6 | 1 | 45 |
| 7 | 1 | 23 |
| 7 | 2 | 54 |
| 8 | 1 | 9 |
| 8 | 2 | 24 |
| 9 | 2 | 6 |
| 9 | 3 | 15 |
| 10 | 4 | 4 |

All unions of size at least 11 and the 52 size-10 unions containing three
pencils are dead. Masks containing no pencil may still be useful intermediate
signals and cannot be excluded merely for having zero direct coverage.

For a fixed output `p`, if the exact pencil is absent, each covering clause
`U` properly contains `N(p)`. Choose one extra line from each such clause.
For every negative cap `D` disjoint from `N(p)`, some chosen line must lie
outside `D`. The enumerated minimum transversal size is 3, with 12 minimizers,
for every point. Thus at least three proper clause signals are necessary.
Replacing a clause by a smaller one improves coverage, but there is no claim
that such replacement preserves the cost of its union DAG.

If every clause for `p` contains some other pencil `N(q)`, choose one such
partner point per clause. For every negative cap `D` under consideration,
some chosen partner must have its pencil disjoint from `D`. These partner
transversals have minimum size 9, with four minimizers, for every point.
Consequently this special case needs at least nine distinct clause signals
for output `p`. Gates may serve several outputs, so this per-output condition
alone does not imply a global gate lower bound.
