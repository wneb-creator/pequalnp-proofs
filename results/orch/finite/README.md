# Finite ownership checks

These are reproducible computational checks, not Lean lower-bound certificates.

Run from the repository root:

```
python3 results/orch/finite/semantic_graph_search.py --n 4 --max-gates 4
python3 results/orch/finite/semantic_graph_search.py --n 5 --max-gates 5 --check-cycle-six
```

The script enumerates triangle-free graphs with no four-cycle on the labelled vertex set. It performs breadth-first search on the set of available truth tables. Each step adds an AND or OR of two available signals, or constant true. Constant false is available without a gate because the circuit model allows a missing wire. Copies and semantically duplicate signals are omitted: substituting the already available wire removes such a gate. Nullary and unary gates therefore give no additional smaller cases.

State deduplication preserves the available truth tables and the number of gates, so it preserves existence of a circuit of a given size. It retains one concrete witness per state. The ownership test uses the full strict structural cone of each AND gate. The search does not claim every minimal circuit has ownership; it checks that each recorded minimum-size witness has it.

Results are in `n4.log` and `n5.log`:

- All 38 eligible labelled graphs on four vertices were found with at most four gates. Every stored minimum-size witness has every AND owning an edge.
- All 291 forests on five vertices were found with at most five gates. Every stored minimum-size witness has every AND owning an edge.
- The remaining 12 eligible labelled graphs on five vertices are copies of the five-cycle. After enumerating 958,669 five-gate semantic states, the script tries every possible sixth AND/OR gate for one labelled five-cycle and finds none. The other copies follow by renaming vertices.
- The separate Lean component `../lemmas/counterexample_route.lean` checks a seven-gate five-cycle circuit's function, monotone fan-in-two status, and ownership. Its minimality is established here computationally, not by that Lean file.

`all_graphs_n4.py` and `all_graphs_n4.log` broaden the same method to all 64 labelled simple graphs on four vertices. The minimum-size distribution is 0:1, 1:6, 2:12, 3:10, 4:16, 5:18, 7:1; the unique seven-gate case is the complete graph. Every retained minimum witness is ownership-good and has every AND false on singleton inputs. The `bad_minimum` diagnostic examines final transitions from retained representative histories only. Its empty result does not assert that every minimum circuit is good: semantic state deduplication does not retain every structural history.

No counterexample to L-meta-1772 was found in these checks.
