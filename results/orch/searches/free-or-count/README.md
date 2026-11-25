# Free-OR counted-AND search

This is computational evidence, not a Lean proof and not a resolution of L-meta-2585.

For a circuit with at most k AND gates, order the AND gates topologically and flatten
each OR-only operand cone. Each AND operand is an arbitrary OR of original inputs
and earlier AND outputs. The final output is an OR of the same kinds of wires.
For our targets, all singleton assignments are rejected, so original inputs cannot
occur in that final OR. Fewer than k ANDs can be padded by unused zero gates. Thus
the encoding has no upper bound on the original number of OR gates.

For --dual, the target is the vertex-cover function AND_edges(x_p OR y_l), which
is the Boolean dual of the incidence function. Counting its AND gates therefore
counts OR gates of the original circuit, with the original AND count unrestricted.
The dual also rejects all singleton assignments for the present instances because
their forced diagonal matching has size at least two. Do not apply the output
omission argument to a dual target having a one-vertex cover.

Dynamic instances force a diagonal perfect matching and prohibit every C4.
They are not a census of all n-by-n incidence graphs. A violation of the AND
bound with vertex-cover number n restricts to the endpoints of a maximum
matching and can be relabeled into this dynamic model. An OR-edge-count violation
need not survive that restriction.

All instances enforce exact truth on every one of the 2^(2n) assignments, not only
on pairs. Every SAT control was reconstructed and checked on every assignment,
and every original CNF clause was checked against its model.

## Frozen invocations and outcomes

Each invocation is `python3 free_or_and.py n k stem [options]`.

| Stem | n | k | Options | Solver result |
|---|---:|---:|---|---|
| dynamic4_k3 | 4 | 3 | none | UNSAT, exit 20; 45s wall budget |
| matching4_k4 | 4 | 4 | --fixed matching | SAT, exit 10; 15s budget |
| cycle3_k3 | 3 | 3 | --fixed cycle | SAT, exit 10; 15s budget |
| cycle3_k2 | 3 | 2 | --fixed cycle | UNSAT, exit 20; 15s budget |
| cycle3_or5 | 3 | 5 | --dual --fixed cycle | SAT, exit 10; 20s budget |
| cycle3_or4 | 3 | 4 | --dual --fixed cycle | UNSAT, exit 20; 20s budget |
| dynamic5_k4 | 5 | 4 | none | UNKNOWN, timeout exit 124 after 120s wall |
| dynamic4_or6 | 4 | 6 | --dual --min-edges 8 | generated only, never run |

Solver executable: `/tmp/oec/pequalnp-pilot-86/lean-4.36.0-linux/bin/cadical`.
Every solver run used `nice -n 15 timeout <budget> <solver> <stem>.cnf` with
complete stdout/stderr redirected to the corresponding files. Build stdout/stderr
are also complete. `verify_free_or.py` independently checks SAT controls.
Status_review independently reviewed the encoding and reran all three SAT controls;
its complete logs are `review-controls.stdout` and `review-controls.stderr`.

The dynamic4 UNSAT result supports AND >= vertex-cover for every C4-free bipartite
graph with vertex-cover at most four, irrespective of total vertex count:
restrict a hypothetical violation to endpoints of a maximum matching of size m;
if m < 4, append 4-m independent edges. Their standard implementation adds 4-m
ANDs (OR count is free), giving a forbidden 4-by-4 target with at most three ANDs.
The C6 dual UNSAT result supports OR >= 5 for C6 with no AND-count restriction.
These are external solver conclusions, not formal lower bounds.

## Mathematical review

No general dirty-block charge was obtained. Singleton and pair signatures at a gate
do not determine whether it accepts independent triples or larger sets. A potential
depending only on those signatures cannot certify exactness of arbitrary dirty
intermediate functions. Any complete global-family potential must also represent
the higher independent sets, or derive why they can be discarded without losing
the size budget; the current normalization hypotheses do not give that fact.

The unrestricted OR inequality has a useful exact dual formulation: every monotone
circuit for AND_edges(x_p OR y_l) would need at least |E|-1 AND gates. The clauses
are irredundant, but their count alone is not additive under OR: distributing OR
over two CNFs forms a Cartesian product of clauses. This is precisely where a
simple clause-count potential breaks down.

Primary research checked 2026-11-25: Nets Hawk Katz, On the CNF-complexity of
bipartite graphs containing no K2,2's, https://arxiv.org/pdf/1206.6068. Its CNFs
are intersections of clause graphs and only represent the graph on cross-pairs.
It constructs high-average-degree C4-free examples with logarithmically many such
clauses. This is not an exact-circuit counterexample: those clauses need not reject
all larger independent assignments. The representation/computation distinction is
essential before using this source for an unrestricted cost argument.
