# L-meta-2583 semantics audit

## Statement and definitions

The circuit is monotone, has exactly two inputs per gate, and all wire reads point backward (`TopForm.IsAO2`). Input wires are free; every AND/OR gate counts. Constants and NOT gates are excluded. Point inputs occupy `Fin.castAdd N p`, line inputs `Fin.natAdd N l`; the two ranges are disjoint even when N=0.

`ReadK.IsReadK` uses the actual prime implicants of the circuit function. Its proof vectors jointly bound both variables within one proof tree. The weaker per-variable recursion `eachReadsAtMost` is not used. Thus no separate-tree loophole is available. Forward-wire defaults, zero-input gates, and NOT behavior cannot create counterexamples under IsAO2.

The plane hypotheses are nondegenerate: q>=2, N=q^2+q+1, every line has q+1 points, and every distinct pair of points has a unique joining line. Counting gives the usual dual regularity and intersection properties; no missing nondegeneracy hypothesis was identified.

Choosing D=C is unjustified: duplicating an output via an AND gate preserves its Boolean function while doubling every leaf multiplicity in its proof trees. The task permits replacement by a smaller circuit, so this is only a warning against a direct proof, not a counterexample to the posted statement.

## Checked partial

`semantics_prime_2583.lean` proves, for any incidence relation and any circuit computing its incidence function:

1. Prime implicants are exactly the pairs `{point p, line l}` with I p l.
2. Read-1 is equivalent to the joint read-1 vector check for each incident pair.

No plane axioms or circuit-shape assumptions are needed for these two facts. They reduce the ReadK obligation from all subsets of 2N inputs to the incidences. The proof uses only Mathlib.Tactic and PEqualNP.Defs and is in the intended auxiliary namespace.

Validation: `lake env lean ../results/orch/lemmas/semantics_prime_2583.lean` exited 0 with empty stdout and stderr on 2026-11-25. Complete final logs: `/tmp/oec/pequalnp-pilot-128/semantics-prime-2583-run2.stdout` and `.stderr`. Theory agent independently reviewed it and reported PASS. This is a helper result, not a proof of L-meta-2583.

## Remaining obstruction

Per-incidence duplicate-leaf pruning is local, but a shared gate can require different pruning choices for different incidences. For example `(a OR b) AND (a OR c)` accepts singleton a only by reading a twice, and also accepts the pair {b,c}. A later line product can make that extra pair harmless through absorption. A size-preserving transformation must control this sharing uniformly; the prime-implicant characterization alone does not do so.

## One dirty AND: checked semantic classification

New checked file: `semantics_one_dirty_2583.lean`. Consider a dirty gate H=(OR A) AND (OR B), followed by blocks H AND (OR R_i). When A and B are disjoint, its accepted input pairs have exactly one endpoint in each side, and one endpoint in R_i. The oriented pair set is

`((A ∩ R_i) × B) ∪ (A × (B ∩ R_i))`.

Taking the union over all such blocks gives U×B ∪ A×V, where U=A∩union(R_i), V=B∩union(R_i). If every block lies below the graph function, every displayed pair is a graph edge. In a C4-free graph, |B|>=2 forces |U|<=1, and |A|>=2 forces |V|<=1. Thus, when both dirty operands have at least two variables, their entire dependent quadratic contribution is at most one double star, regardless of the number of these blocks. These facts compile against actual `TopForm.NoFourCycle` and the root Boolean-input model.

This is a semantic classification, not a size-preserving circuit transformation. Two gaps remain explicit:

- If A={a}, the useful leaf set is V=B∩union(R_i), which need not be an already available OR wire. Using all of B can introduce nonedges. Extracting this intersection may require changing a shared OR network.
- Actual top-form circuits can have an operand `(H OR U)` before a top AND, not just H directly; expanding this algebraically can increase gate count. A uniform circuit-level transformation must control those OR paths and their other uses.

A possible budget source in the bipartite setting: an OR wire containing variables of both colors is true on both monochromatic all-true assignments, so it cannot feed a clean AND whose other operand is OR-only and nonempty. Consequently some mixed OR gates near the dirty-gate region may become removable when the region is replaced. This observation has not yet been formalized into a size bound.

Validation: `lake env lean ../results/orch/lemmas/semantics_one_dirty_2583.lean` exited0 with empty stdout/stderr; complete logs are `/tmp/oec/pequalnp-pilot-128/semantics-one-dirty-2583-run1.stdout` and `.stderr`.
