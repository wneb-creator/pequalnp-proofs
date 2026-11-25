# Checked paired-neighborhood certificate rule

`PairedExactFramework.lean` adds one sound clause family to the compact
certificate framework for the exact L-meta-9775 graph.

Assume a normalized strict live DAG computes the graph function and has
`Bzero <= 1`. For an independent set `P`, take two inputs `i,j` in its
`ineligSet`, with a vertex of `P` adjacent to `j` but not `i`. The generic
`sem_shared_empty` theorem implies that either the exact `P`-neighborhood of
`i`, or that of `j`, occurs on a circuit wire next to an AND gate. Selecting
`x in P` adjacent to `i` and `y in P` adjacent to `j` gives a disjunction:
some enumerated slot for `x` has the first neighborhood, or some slot for `y`
has the second. `Layout.exact_from_chain` checks membership of that AND input
in the appropriate semantic slot set; `Layout.paired_exact` proves the result.

`BudgetScheme` has two constructors. `plain` uses an existing scheme with
`exactAt` disabled. `pairedExact x i y j p` uses the new disjunction, and its
finite `enabledBudget` check verifies every geometric condition above.
`inputsOKBudget` checks the correspondence between these semantic clauses and
the numbered Boolean facts in a certificate. `book_start_budget` establishes
validity of the initial clause database; the unchanged resolution replay
then establishes any contradiction. External SAT output alone is not a Lean
proof: the generated data must pass these kernel-checked certificate lemmas.

The layout constructor in `WeakCompactFramework` accepts the general budget
identity `Bplus + |ineligSet| = 14 + k`. The paired rule itself requires only
`Bzero <= 1`, rather than equality to zero. The original framework remains
available for the stronger zero case.

All three framework modules exported successfully. The paired module's
successful compile has empty stdout and stderr. Axiom checks of its semantic
rule, initial-database soundness theorem, and final contradiction theorem use
only `propext`, `Classical.choice`, and `Quot.sound`. Complete diagnostics are
preserved beside this document. No final L-meta-9775 result is asserted by
these framework modules alone.
