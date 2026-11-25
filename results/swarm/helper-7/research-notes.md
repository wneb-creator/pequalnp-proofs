This is a partial research record for L-meta-3566, dated 2026-11-25. No full proof or
counterexample is asserted. Solver UNSAT results are not certified Lean proofs.

The extended search scripts preserve the original full-function boundary: every edge
is positive, and every maximal independent set is negative. `count_query.py` adds
optional lexicographic gate order, an input-occurrence budget, and AND-count bounds.
`single_query.py` restricts one selected input to exactly one reader of a selected
operation. Its individual cases are conditional searches, not global lower bounds.

The general bound used by `--mis-lower` is valid for monotone fan-in-two circuits:
if there are A AND gates, globally choose one parent at every AND. Each of the at
most 2^A choices gives an OR-only circuit whose output is above the original
function. At any false assignment, choosing a false parent at each false AND makes
the selected circuit false there. The original function is therefore the conjunction
of these OR-only clauses. Each clause has at most one maximal false assignment;
every maximal false assignment of the original function must be one of these.
Thus M <= 2^A, where M is the number of maximal false assignments. For a graph
function these assignments are exactly the maximal independent sets. This reasoning
does not require bipartiteness or absence of four-cycles. It is used only with the
complete graph boundary, never with a partial CEGAR negative sample.

All live fan-in-two k-gate DAGs have at most k+1 original-input operand occurrences: each of
the k-1 non-output gates must occupy at least one later operand slot, leaving at
most 2k-(k-1) slots for original inputs. Trailing copies preserve this bound. The
`--input-budget` counter encodes it. Explicit `--min-and` and `--max-and` restrictions
are labeled conditional unless the enabled general bound justifies the minimum.

Current targets and independently enumerated graph data:

| Fixture | Vertices | Edges | Cover number | Maximal independent sets | Gate target |
| --- | ---: | ---: | ---: | ---: | ---: |
| Heawood12noninc | 12 | 15 | 6 | 26 | 19 |
| GP8del_inc | 14 | 19 | 7 | 39 | 24 |
| GP8del_noninc | 14 | 18 | 7 | 44 | 23 |
| C6book3 | 14 | 16 | 7 | 41 | 21 |

Each target is one below edges + cover number - 1. All four graphs are bipartite
and have no four-cycle. These searches were still running at this snapshot.
The full solver diagnostics remain in the job workspace; only portable scripts,
graph fixtures, and small checked records are committed.

Existing-source discoveries retired several earlier targets:

- `L_meta_615.lean` gives the general three-path theta lower bound. In particular,
  theta333 uses p=q=r=2 and cover number 4, giving 12 gates.
- The internal `fano27` helper in `L_meta_7945.lean` gives the unconditional
  27-gate Heawood lower bound; this refers to that helper, not the conditional
  final theorem of the file.
- `L_meta_723.lean` gives the unconditional 15-gate subdivision-of-K4 bound.
- `L_meta_9732.lean` gives the unconditional 21-gate bound for Heawood12inc.
  `h12inc-9732-isomorphism.json` records the exact relabeling, checked on all 144
  ordered vertex pairs. This helper inspected the source statement and graph
  correspondence; independent swarm helpers additionally reported kernel checks.

Those source results are separate from this helper's timed-out or interrupted SAT
queries. The local UNKNOWN results are not promoted to UNSAT.

Heawood12noninc is the K3,3 graph with each edge of a perfect matching replaced
by a length-three path. `h12noninc-K33-isomorphism.json` records an independently
checked relabeling and the canonical edge list. Our total-gate search and the
separate free-OR, five-AND search investigated by other helpers concern this same
graph function. Their gate-count restrictions are different.

A bounded repository census found no applicable existing lower bound for either
GP8 deletion. It checked 112 files mentioning exact dimension 14, ten nearby
size-bound candidates, strict numeric edge lists, 835 lists of fourteen numerical
adjacency masks, and thirteen numerical `Nat.testBit` masks. This was a textual
search, not an exhaustive theorem search. Different encodings or implicit dimensions
may have been missed. Source candidates were inspected without fresh compilation.
`gp8-source-literal-census.json` contains the two closest nineteen-edge graphs.
They differ from GP8del_inc: the sorted distances among its four degree-two vertices
are [3,3,3,3,4,4], versus [2,2,3,3,5,5] in L_meta_9777 and [1,3,4,4,5,5] in
L_meta_9774. The respective six-cycle counts are 12, 13, and 14. GP8del_noninc has
eighteen edges and therefore cannot match either nineteen-edge graph.

General source bounds requiring read-once circuits, pair-clean AND gates, top form,
or a lift fixed point were not treated as unconditional bounds for the current
searches. In particular, the final theorem of L_meta_2399 only handles cover number
at most five; no general AND >= cover-number assertion is used here.

Portable additional checks, from this directory with Kissat on PATH:

```
python3 test_input_budget.py
python3 test_mis_lower.py
python3 count_query.py --graph C6 --k 7 --min-and 0 --mis-lower --lex --input-budget --seconds 60
python3 single_query.py --help
```

The exact counter tests and small-circuit checks are implementation validation,
not a formal proof of the general synthesis normalization. Independent review
covered the mathematical arguments, CNF clauses, padding, explicit restrictions,
all new fixtures, and execution from a different directory.
