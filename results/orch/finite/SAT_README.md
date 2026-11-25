# Bounded monotone graph-circuit searches

These are computational experiments. No solver result here is a Lean or LRAT certificate, and no timeout is evidence of unsatisfiability.

Three encodings are retained:

- `sat_baseline.py`: binary AND/OR gates, free constants, ordered operands within a gate, and no unused gate. This encodes at most the requested number of gates by allowing repeated copies at the end.
- `sat_ordered.py`: additionally offers `--ordered`, a topological gate-order symmetry, and the singleton-AND query.
- `sat_normalized.py`: additionally offers `--distinct-prefix` and `--pair-orbits`, for irredundant minimum-circuit searches.

The programs require Z3's Python package. Solver version, public release URL and archive digest are recorded in `sat_solver.json`. In this job the package was extracted directly from the public GitHub release wheel into scratch; no package index was used.

Example commands after making `z3` available on `PYTHONPATH`:

```
python3 results/orch/finite/sat_baseline.py cycle5 6 --timeout 120
python3 results/orch/finite/sat_baseline.py cycle5 7 --timeout 120 --require-bad-own
python3 results/orch/finite/sat_ordered.py cycle6 8 --timeout 90 --ordered --require-bad-own
python3 results/orch/finite/sat_normalized.py theta233 10 --timeout 180 --ordered --distinct-prefix --pair-orbits
```

Every output records its graph, edge list, number of gates, flags, solver result, elapsed time and timeout reason when applicable. SAT models are independently re-evaluated on all Boolean assignments, and their strict AND-ancestor cones are reconstructed to check ownership. The reported `tau` is computed by exhaustive independent-set enumeration, not assumed.

## Why the graph samples suffice

For a monotone Boolean circuit, equality with the edge function is equivalent to returning true on every two-vertex edge input and false on every maximal independent-set input. Every positive assignment contains an edge. Every negative assignment is an independent set and extends to a maximal independent set in a finite graph. Monotonicity supplies the two implications. The code enumerates every subset of vertices and retains every inclusion-maximal independent set, so the negative census is complete. Singleton queries add all singleton inputs as redundant negative samples.

## Constants, copies and unused gates

False is free in the public circuit model through a missing wire. Giving true for free cannot lower the minimum of a nonconstant graph function: propagate constant inputs through AND/OR gates, remove copies and constant gates, and retain the nonconstant output. No new gate is needed. A minimum circuit for a nonempty graph therefore has no constant or copy gates. Gates unused by the output may likewise be deleted.

The baseline excludes a gate whose sampled value is identically false or true. If such a gate existed in a minimum circuit, replace it by that free constant, remove it, propagate constants, and obtain a smaller monotone circuit agreeing with the graph function on every sample. The sample argument above makes its entire output function exact. Thus the exclusion preserves every globally minimum candidate. For an at-most-k existence query, normalize a smaller candidate and pad it with copies of its nonconstant output; this gives exactly k slots while retaining the baseline restrictions.

## Ordering the gates

Within a gate the operands may be sorted because AND and OR commute. For `--ordered`, repeatedly choose the ready gate with the smallest key (maximum operand index, minimum operand index, operation). A gate that becomes ready after producing wire t has maximum operand index t; all gates already ready have smaller maximum operand index. Thus maximum operand indices never decrease. For a fixed maximum operand index, all relevant gates are already ready together, so the minimum operand and operation can also be ordered. This only renumbers a DAG and preserves its structural cones and ownership. All retained gates reach the output, so the output is last.

## Distinct sampled signatures and an active prefix

Under `--distinct-prefix`, active gates form a prefix and each active gate's sampled truth table differs from every preceding wire, including inputs and constants. A duplicate sampled signature in a globally minimum circuit is impossible: replace the later gate by the earlier wire, delete it, and use sample sufficiency to obtain a smaller circuit for exactly the same graph function. Repeating this operation normalizes any witness without increasing its size.

Inactive suffix slots are forced OR copies of the preceding wire. They are not part of the represented circuit: truncate the suffix and use the last active output. They create no AND ownership event, and cannot lie in an active gate's cone. This permits any normalized circuit of size at most k to occupy k solver slots. A SAT result must be read using its reported `active` flags.

## First-gate pair orbits

`--pair-orbits` enumerates all graph automorphisms by backtracking, checking both adjacency and non-adjacency against every previously mapped vertex. It then enumerates the orbits of unordered pairs of distinct vertices and chooses each orbit's least pair in (maximum endpoint, minimum endpoint) order.

In a minimum circuit the first gate combines two distinct input vertices. Among all automorphic images and canonical topological orders, choose one whose first input pair is least. That pair must be its orbit representative: otherwise an automorphism lowering it, followed by reordering ready gates, would give an even smaller first pair. This restriction therefore preserves a representative of every globally minimum circuit up to graph automorphism and gate renumbering. Both ownership and being true on some singleton are invariant under these transformations.

## Limits of property-constrained conclusions

Signature pruning and first-pair restrictions are justified for globally minimum circuits. A SAT model with a non-owning AND is not a refutation of the target, which asks for the existence of a good minimum circuit. A property-constrained UNSAT result at a size not established as minimum does not claim that all arbitrary circuits of that size satisfy the property. Search timeouts remain unresolved.

## Alternate SAT engine

`sat_external.py` accepts graph data from `--graph-json`, using the same normalized encoding. `sat_cadical.py` additionally exports its assertions to DIMACS through Z3's simplify, propagate-values, solve-eqs, bit-blast and Tseitin-CNF tactics. `cadical_solver.json` records the CaDiCaL release, source digest, conversion pipeline and exact CNF digests. The CNF files themselves remain in scratch and can be regenerated with `--dimacs`.

For example, append `--dimacs <file.cnf>` to a normalized query, then run `cadical -t 300 <file.cnf>`. Exit 10 means SAT, 20 means UNSAT, and an interrupted/limited run is unresolved. Complete solver logs are retained. No DRAT or Lean certificate has been generated.

For a SAT result, rerun the same query with both `--dimacs <file.cnf>` and `--cadical-output <solver.log>`. The recovery code first requires the regenerated CNF bytes to be identical. It verifies every DIMACS clause under the printed assignment, constructs the Boolean model using the actual auxiliary declarations, converts it through the tactic model converter, and checks every original constraint. It then runs the same full Boolean truth-table and ownership checks as the direct solver. This recovery path was validated on the four-gate path circuit.
