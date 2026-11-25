# Local repair SAT research

These scripts search rewiring of selected gates of the 64-gate near-miss while fixing all other gates. The finite truth-table basis consists of 52 positive edges and 704 maximal independent sets. Both directional derivative recurrences must be false. Operands are distinct earlier wires and every gate is AND or OR.

Solver UNSAT excludes only the selected neighborhood under its encoded constraints. It is not kernel checked and is not a proof of L-meta-2602. A timeout is no mathematical verdict. No exact counterexample has yet been found.

The six-gate neighborhood 28,29,30,61,62,63 returned UNSAT after refinement to 395 boundary rows. Larger neighborhoods remain under investigation. metadata.json records complete-source and CNF hashes; large CNF files remain in scratch. Solver stdout and stderr are retained without truncation.
