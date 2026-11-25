# L-meta-1772 finite searches

These are computational checks, not Lean proofs or a refutation of the assigned statement.
All searches and tool versions were recorded on 2026-11-25 UTC.

## Solver

`circuit-sat.py` emits a DIMACS instance and invokes CaDiCaL 3.1.0. The solver was built in job scratch from the official GitHub `rel-3.1.0` archive:

https://github.com/arminbiere/cadical/releases/tag/rel-3.1.0

No system package was installed. To rerun with an existing solver, set `PNP_CADICAL` to its executable path and `PNP_SEARCH_DIR` to an output directory. Otherwise the script defaults to its own directory and expects `cadical-rel-3.1.0/build/cadical` there.

For example:

```sh
python3 circuit-sat.py --graph cycle5 --gates 7 --seconds 60
python3 circuit-sat.py --graph cycle5 --gates 7 --unowned-and --seconds 60
python3 circuit-sat.py --graph cycle5 --gates 7 --unsound-and --seconds 60
python3 circuit-sat.py --graph cycle7 --name cycle7canonical --gates 9 --canonical-first --seconds 120
python3 circuit-sat.py --graph petersen --gates 19 --seconds 300
```

The archived CNF files are the exact instances corresponding to the saved solver logs. The encoder evolved during the run; its current version includes additional gate-order symmetries, so rerunning an earlier command can produce a different but intended equivalent canonical search space.

## Encoding and limits

Every gate is binary AND or OR on two distinct earlier wires. Output is the last gate, and every earlier gate is read. Gates are ordered by their larger operand; version 2 also orders tied gates by the smaller operand and operation. These are standard normalization assumptions for minimum nonconstant monotone circuits, but the normalization argument is not Lean checked here. Therefore the UNSAT findings are explicitly about this normalized model.

Truth-table tests consist of every edge assignment (must accept) and every maximal independent set (must reject). These characterize the graph function for a monotone circuit. Every SAT witness is also evaluated independently on all `2^n` inputs.

`--unowned-and` forces at least one AND gate to own no graph edge. For each positive edge input, an auxiliary signal records whether an earlier true AND occurs anywhere in a wire's syntactic cone. The signal propagates through both inputs even when that input does not contribute to the gate's value. This matches the strict-cone ownership definition.

`--all-owned` requires every AND gate to own an edge. `--dirty-and` forces an AND true on a singleton input. `--unsound-and` forces an AND true on an independent input. The latter is tested on maximal independent inputs; monotonicity suffices. `--singleton-safe` and `--sound-ands` impose the opposite restrictions.

`--canonical-first` adds symmetry restrictions intended for cycles and the Petersen graph only. The C7 canonical result uses them. It is a search result, not a certified lower bound.

CaDiCaL exit 10 means SAT, 20 means UNSAT, and 0 at the imposed wall-time limit means UNKNOWN. A timeout is never evidence of a lower bound.

## Results saved so far

| Graph and condition | Result |
| --- | --- |
| All labelled no-C3/no-C4 graphs on 1,2,3,4 vertices | Semantic-state BFS found minimum ownership witnesses for 1,2,7,38 graphs respectively |
| C5, 7 gates | SAT; all 32 inputs validated; all ANDs own edges |
| C5, 6 gates | UNSAT in the normalized model |
| C5, 7 gates, singleton-dirty AND | UNSAT in the normalized model |
| C5, 7 gates, unowned AND | UNSAT in the normalized model |
| C5, 7 gates, unsound AND | UNSAT in the normalized model |
| C6, 7 gates | UNSAT in the normalized model |
| C6, 8 gates, singleton-dirty AND | UNSAT in the normalized model |
| C7, 9 gates, canonical-first symmetry | UNSAT in the normalized model |
| Petersen, 19 gates | UNKNOWN after 300 seconds of SAT search; also UNKNOWN after 180 seconds of MILP search |

No counterexample to L-meta-1772 was found. The separate Lean file `../lemmas/Counterexample.lean` checks only the explicit seven-gate C5 construction, its function, ownership and size; it does not assert minimality.

Full solver stdout and stderr are retained in the `*-solver.log` files. JSON summaries contain independently checked SAT models where found. `sha256.json` records file hashes for the first archived batch.
