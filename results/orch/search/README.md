# Finite searches for L-meta-2685

These artifacts test selected C4-free bipartite incidence functions. They do not prove the
universal posted statement. Every UNSAT result is **computed, not Lean-certified**. Every
time limit is **UNKNOWN**, with no conclusion about existence.

The complete nonempty 3-by-3 census has 15 types up to row/column permutations and exchange
of the two sides. The complete nonempty 3-by-4 census has 39 types up to row/column
permutations. All nontrivial types were tested for an AND/OR circuit with one fewer gate
than `number of edges + maximum matching size - 1`; all those queries returned UNSAT.
The single-edge type separately cannot be computed by a zero-gate circuit: its output
would be one input bit or the constant false. An initial time limit for the 3-by-4
six-cycle-with-pendant-edge case was later resolved by the exact boundary encoding.

Larger selected cases include the 8-cycle and the vertex-edge incidence graph of K4.
Their individual verdicts, budgets, and full solver logs are recorded in `manifest.json`.
A found 11-gate 8-cycle circuit and an 8-gate 6-cycle circuit were independently evaluated
on every Boolean assignment. No counterexample to the posted statement was found.

## Encoding and limits

Each gate chooses AND or OR and two earlier wires. The two operand indices are ordered;
repeated operands are allowed. Its truth values are constrained by explicit Boolean
multiplexer and gate clauses. The final gate is the output. Any smaller nontrivial
circuit can be padded by duplicate-operand gates, so a query at size `k` covers sizes
below `k` as well. There are no NOT gates or constants.

The optional boundary encoding imposes true only on assignments consisting of the two
ends of an edge, and false on each maximal independent-set assignment. Since every
candidate circuit is monotone, these rows imply equality on every assignment. The generic
finite hypergraph version of this fact is Lean-checked as
`PEqualNP.Outside.L_meta_2685.monotone_eq_of_hypergraph_boundary` in
`../lemmas/counterexample-route.lean`. This does not certify the solver's UNSAT results.

The optional canonical-order encoding orders adjacent independent gates lexicographically
by operand indices and operation, and requires each non-output gate to have a later
reader. A size-minimal circuit can discard gates outside the output cone; smaller circuits
can then be padded by copies of the output. Among topological presentations, a
lexicographically least presentation has the stated adjacent order: an inverted independent
pair could otherwise be swapped, renaming subsequent wire references. Original encodings
without this optional condition and their full logs are retained separately.

## Reproduce

`synth-small.py` generates DIMACS and invokes CaDiCaL. It accepts `--solver` and
`--output-dir` to avoid depending on the original container paths. `--emit-only` regenerates
the CNF without invoking a solver. `manifest.json` contains each command as an argv array,
the CNF hash, result hash, and full solver-log hash. Replace `REPRO_DIRECTORY` and
`CADICAL_EXECUTABLE` with suitable paths. Binaries and regenerable CNFs are omitted.

```
python3 enumerate-c4free.py 3 3 --transpose --output census-b3-reproduced.json
python3 enumerate-c4free.py 3 4 --output census-b34-reproduced.json
python3 verify-search.py
```

The census generator was rerun independently and its JSON data matched the original
censuses. `verify-search.py` checks archived hashes, C4-freeness, solver status text,
coverage of both censuses, and every row of each recorded SAT circuit's truth table.
Full solver stdout/stderr is in `logs/`; compact decoded results are in `records/`.
