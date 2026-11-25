# Strengthened score: complete-CNF stress tests

These completed finite counts test the proposed stronger score `2B+M+J`, where J additionally charges positive-singleton-output AND gates and AND gates with exactly one singleton-negative operand. They do not prove or refute the posted statement or the stronger score inequality in general.

The complete prime CNF has one clause for each maximal false assignment. For a bipartite graph, enumerate the chosen left subset A and let B be every right vertex outside N(A). The resulting independent set is maximal precisely when every left vertex outside A has a neighbour in B. This enumerates all maximal independent sets exactly, with no 2^(p+q) truth-table enumeration.

Results: K4 incidence has 12 maximal false assignments; PG(2,2) has 37; PG(2,3) has 704. Their |E|+tau values are respectively 16, 28, and 65. The incidence planes are regular bipartite graphs with equal colour classes, so Hall's condition gives a matching saturating a colour class. K4 incidence also has a matching saturating its four vertex inputs.

A conjunction network combining m singleton-positive clause outputs has AND charge at least m when the final singleton support is empty: each binary AND's `2B+J` charge is exactly the number of its positive children minus the positivity indicator of its output. Summing cancels internal wires; positive fanout only adds nonnegative terms. Distinct nontrivial pure-OR clauses each require a distinct counted positive-positive OR somewhere in their ancestry, so M is at least m. Hence the full-CNF construction has score at least 2m: 24, 74, and 1408, above the targets in all three cases.

This rules out only the straightforward complete-CNF construction. A general circuit may mix dirty ORs with ANDs on singleton-negative functions and need not expose every prime clause. No search over those general circuits is claimed.

The exact Python counting program and its complete output are included. The score argument is mathematical reasoning, not a Lean proof. The run records the already completed CNF checks after root requested freezing during lease recovery.
