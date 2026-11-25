# Finite check of exactly one NOT

All26 connected bipartite C4-free graph types on2–7 vertices were checked for a circuit with exactly one NOT and fewer than m+tau−1 gates, where m is the edge count and tau the minimum vertex-cover size. Every full truth table is constrained. This is finite SAT solver evidence, not a Lean certificate and not a general NOT-elimination theorem. The counts by vertex number2–7 are1,1,2,3,7,12. An independent full-isomorphism check confirmed coverage of all725 valid labeled bipartite matrices by these representatives.

The original queries returned24 UNSAT, one trivial empty gate budget with one required NOT, and one timeout. The remaining seven-vertex graph was resolved by two normalized UNSAT queries: zero NOT at7 gates (covering a pruned unused NOT) and one output-reachable NOT at8 gates. Cone pruning, identity padding and Kahn ordering by maximum actual fanin were independently audited. Thus all26 tested graphs have no such exactly-one-NOT improvement under the solver model. This does not address circuits with two or more NOTs or the14-input leased target.

Source, complete solver diagnostics and command lines, graph data, schemas, summaries and CNF hashes are retained. Heavy CNFs remain in scratch.
