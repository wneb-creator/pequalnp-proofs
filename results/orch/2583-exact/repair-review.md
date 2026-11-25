# Independent SAT repair encoder review

Verdict: PASS as a bounded-neighborhood search and candidate validator. This review is not a Lean proof of a circuit lower bound.

Reviewed source `repair.cpp`: SHA256 `9258993df6c9cd2e8b9b63e86431a3111dfa4d7acabea26a83fe2c58790d6891`.
Reviewed `prepare.py`: SHA256 `17ca91e1375c7da3f1a96dbe54f7510f3cc0c9a33f72efb51fd8e5649967cfd8`.
Reviewed plane data `../2583-search/plane3.json`: SHA256 `6cf683f013828f4ee73d9152679843ee3399a5c6dca77f0fca45dfdef1a2a252`.

The exact-one prefix clauses enforce prefix[i] iff at least one selector through i, prohibit another true selector after a true prefix, and force the final prefix. The prefix used in the fanin ordering therefore correctly enforces left≤right, including equal fanins. The at-most-k forward sequential counter has sufficient implications to detect k+1 true changes; each assignment with at most k has a prefix-count auxiliary witness. The change bit is equivalent to at least one difference in operation or sorted fanins from the seed. AND uses a true op variable, OR false, consistently in the row clauses, seed matching and model decoder.

Fanin selectors range only over earlier wires. Both operand mux implications are correct under exact-one selection. All candidate models are evaluated independently on every supplied row, and any failure on an already-encoded row raises an error. More rows are added only after this check. Structural variables are frozen before incremental solving. WITNESS is emitted only after zero errors on the entire supplied basis.

Small exhaustive independent checks passed 126 exact-one selector assignments, 320 at-most-k assignments with existential search over all auxiliary bits, 16 change-equivalence assignments, and 16 guarded gate-truth assignments. Complete output is saved in `/tmp/oec/pequalnp-pilot-98/2583-repair-encoding-review.txt`.

The q3 graph data has 13 points, 13 lines, 52 incidences, four incidences at each vertex and exactly one line through every pair of distinct points. Independently enumerating all 8,192 point subsets from the stored edge relation reproduces exactly the stored 704 maximal false assignments. The 52 minimal true assignments are exactly the edge pairs. Every maximal independent set has right side equal to all non-neighbors of its left side, and its left side equals the reverse closure, so this enumeration is complete. Every false assignment extends to a maximal false assignment; every true assignment contains a minimal true pair. Hence monotonicity of the AND/OR candidates makes agreement on these 756 rows equivalent to agreement on all 2^26 assignments. `prepare.py` transfers all rows, without dropping positives or negatives. The independent data-check record is `/tmp/oec/pequalnp-pilot-98/2583-repair-basis-review.json`.

Search scope remains the fixed gate count, fixed output index, and specified gate-edit distance from the fixed seed. Identity and unused gates are allowed, but changes of topological numbering can change distance. An UNSAT result establishes only absence in this neighborhood. A SAT candidate still requires translation and Lean checking before it can refute the posted statement; these finite Python/C++ checks are not that formal certificate.

Reviewed UTC: 2026-11-25T14:55:34.265205+00:00
