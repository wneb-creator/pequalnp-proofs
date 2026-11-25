# Seven-input computational supplement for L-meta-4675

The earlier25-experiment manifest and all61 hashed files remain unchanged. This supplement records separate new finite results; it is not a proof or refutation of the posted statement.

| Experiment | Result |
|---|---|
| three-four-extremal-census | ASSERTIONS_PASS |
| three-four-nine-census | ASSERTIONS_PASS |
| all-seven-input-graph-census | ASSERTIONS_PASS |
| pendant-known9 | SAT |
| pendant-at-most8 | UNSAT |
| tree-303-known8 | SAT |
| tree-303-at-most7 | UNSAT |
| tree-317-known8 | SAT |
| tree-317-at-most7 | UNSAT |
| tree-318-known8 | SAT |
| tree-318-at-most7 | UNSAT |
| tree-363-known8 | SAT |
| tree-363-at-most7 | UNSAT |
| tree-857-known8 | SAT |
| tree-857-at-most7 | UNSAT |
| tree-858-known8 | SAT |
| tree-858-at-most7 | UNSAT |

C6 plus a pendant edge has no T0 binary AO circuit with at most eight gates in the exact128-row SMT model: UNSAT in81.983 seconds. A pinned nine-gate star circuit is SAT. Six seven-active tree classes each return UNSAT at seven gates; each pinned eight-gate control is SAT and independently replayed on all128 assignments.

The3+4 census checks all4096 graphs:1952 are C4-free. The72 graphs with |E|+tau>=10 form one class, C6 plus a pendant edge. The444 graphs with |E|+tau=9 form seven classes: six seven-active trees and C6 plus an isolated input.

A further census checks every bipartition on seven inputs up to side exchange. Every C4-free graph is a forest, C6 plus an isolated input, or C6 plus a pendant edge. This is a graph classification. Lower-bound forest classes were not all separately synthesized here, and no blanket seven-input solver conclusion is claimed.

Existing `PEqualNP.MetaComplexity.L104` at `lean/PEqualNP/MetaComplexity/L104.lean:9` gives |E|+k<=s+1 for a nonempty acyclic graph whose covers all have size at least k and whose edge function has circuit size at most s. Its model is the same CircuitLowerBounds.Circuit and permits AND/OR/NOT gates, so it includes the test circuits. With six edges and k=3, it independently predicts the tree results. This is a source-level crosscheck, not a newly compiled Lean application.

No dirty-AND, TopForm, minimum, edge-activity, or pivotality restriction is imposed. The only normalizations are output-cone pruning, removal of idempotent ORs, AND-output padding, and topological gate renumbering; all preserve existence at the tested size bound.

Complete stdout/stderr and exact generated SMT are in `counterexample-seven-input-logs/`. Hashes and command arguments are in `counterexample-seven-input-manifest.json`. No binaries or credentials are included.
