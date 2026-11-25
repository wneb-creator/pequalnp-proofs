# Local repair SAT research

These scripts search rewiring of selected gates of the 64-gate near-miss while fixing all other gates. The finite truth-table basis consists of 52 positive edges and 704 maximal independent sets. Both directional derivative recurrences must be false. Operands are distinct earlier wires and every gate is AND or OR.

Solver UNSAT excludes only the selected neighborhood under its encoded constraints. It is not kernel checked and is not a proof of L-meta-2602. A timeout is no mathematical verdict. No exact counterexample has yet been found.

The original seed's six-gate neighborhood 28,29,30,61,62,63 returned UNSAT after refinement to 395 boundary rows, and again with the full 756-row basis and a different operand-order encoding. Distributed-star seed 1 with five free gates 40,41,61,62,63 and seed 3 with five free gates 8,9,61,62,63 also returned UNSAT on the full basis. Wider neighborhoods have timed out; these give no verdict.

metadata.json records source and seed hashes, exact repair arguments, complete round summaries, and CNF hashes. Completed large CNFs are omitted and may have been deleted from scratch to recover disk space; they can be regenerated. Complete solver stdout and stderr are archived in gzip, with both compressed and original byte counts and hashes.

A separate unrestricted nine-gate search for the eight-input double-star graph uses all 256 assignments and both zero derivative recurrences. Its first 90-second run timed out. This smaller graph search is not a theorem about the plane circuit. The double_star_search_v1.py file reproduces the initial full-assignment encoding; double_star_search.py adds an exhaustively tested ten-row boundary-basis mode.
