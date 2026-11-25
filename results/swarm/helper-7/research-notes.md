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
Without a valid global lower-bound justification, an explicit minimum-AND restriction
limits an UNSAT conclusion to the encoded minimum-circuit normal-form subclass.

The Lean helper package `PEqualNP.Outside.L_meta_3566.ReaderCut` proves a further
bound for the actual project circuit model. In any exact AO2 circuit for a graph
with no four-cycle and minimum degree at least two, every input appearing in a
gate with two primary operands occurs at least twice among all operand positions.
The proof includes duplicate operands. Consequently at least n gates read an
original input, and at most C.size - n gates read only internal wires. Neither
minimality nor bipartiteness is assumed. The direct-reader separation theorem,
sole-AND/OR neighbor lemmas, occurrence bound, and weighted counting argument are
all formalized in the named Lean file. The selected-set extension requires degree
at least two only for vertices in a chosen set S, and proves that at least |S|
gates read an input from S. All other vertices may have any degree. The complementary
bound is C.size - |S|. Its 45 helper lemmas passed an axiom audit
using only propext, Classical.choice, and Quot.sound. There is still no final
theorem for L-meta-3566.

The optional `--primary-reader-bound` encoding enforces these occurrence and gate
counts after checking the graph hypotheses. `--edge-pivotal` chooses a minimum
circuit in which every gate is pivotal on some positive edge: forcing that gate
false makes the output false on that edge. Otherwise false replacement and constant
folding would remove a gate. `--dirty-and-two-pivotal` additionally minimizes the
number of globally dirty AND gates among size minima. A dirty AND with just one
pivotal edge can be replaced by the AND of that edge's endpoints, preserving every
positive edge and decreasing all downstream negative-input values. This removes
that dirty AND without creating another, contradicting the secondary minimum.
The resulting existence statement does not assert that every size minimum has
this property. Both options require a nonempty edge set. Their normal-form
arguments and exact CNF implementation were independently reviewed; cut values
are recomputed through the complete suffix, including shared paths. Appended OR
copies remain pivotal and introduce no dirty AND gates.

The optional `--pair-separation` clauses hold for every exact AO2 circuit.
Distinct maximal independent sets have an accepting union. The first wire failing
to preserve their Boolean join must be an AND whose operand states are 10 and 01
on the two sets, in either order. Dually, two distinct positive edges have a
rejected intersection, so some OR gate has those crossing operand states.
The implementation enforces these witnesses on the full boundary and handles
shared subcircuits. Independent tests checked 8,970 small circuits, 1,703,496
clauses and 3,049 invalid witness flips, plus planted C6/C8 circuits.
All constraints together reproduced C8 at-most-10 UNSAT in 8.0605 seconds;
the earlier strongest query took 171.02 seconds. These runs were not a controlled
performance benchmark, and neither includes a formal UNSAT certificate.

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

`h12_and5_reproducer.py` is helper-2's reviewed fixed generator, copied unchanged.
This helper independently inspected the free-OR flattening, disjoint-selector
factoring, greedy ordering and padding arguments, regenerated the exact SMT query,
and reran it with libz3 4.13.3.0. It returned UNSAT in 106.5968 seconds under load.
The small complete output and hashes are in `h12-and5-reproduction.json`.
This is external solver evidence for at least six AND gates on this graph,
with no Lean or DRAT certificate. The active total-19 variant uses `--min-and 6`
with that separate justification, plus the primary-reader and pivotal constraints.
It is not a completed total-gate lower bound or a gap counterexample.
The reproducer needs an installed shared libz3 only when `--solve` is requested;
without it, the standard-library script just generates and hashes the SMT file.

`free_or_and_query.py` generalizes that reviewed generator and reconstructs every
SAT model as an explicit AO2 circuit. It supports a conditional private-OR cost
cap, the exact sum of max(region size - 1, 0) across all AND operand regions and
the output region. AND cap six and private-OR cap fifteen are sufficient for a
21-gate book3 witness. UNSAT with this cap only excludes the encoded witness
family: OR sharing or normalization may change this private cost. Reconstruction
removes false/dead gates and duplicates, shares available OR computations, checks
readback and evaluates all 16,384 inputs. The published
`C6book3-standard-calibration.json` is explicitly a known 22-gate control with
seven ANDs and fifteen ORs, not a six-AND witness. Its full truth table was checked
independently. The restricted six-AND pilot is still running at this snapshot.

The optional `--and-kraft` constraint in this generator uses the general bound
sum over maximal false rows of 2^(equal AND operand count) <= 2^k for k ANDs.
At some AND, any two such rows must have opposite 10/01 states; the corresponding
partial-signature cubes are disjoint. Since 2^e >= e+1, the sum of all equal 00/11
operand counts is at most 2^k - M. This bound includes syntactic false padding.
The implementation uses the complete MIS suffix, exact-width arithmetic and an
explicit contradiction when M > 2^k. It passed independent mathematical/code
review and finite arithmetic tests. For book3 at k=6, its budget is 23.

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
python3 test_primary_reader_bound.py
python3 test_edge_pivotal.py
python3 test_pair_separation.py
python3 free_or_and_query.py --self-test
python3 test_free_or_and_kraft.py
python3 count_query.py --graph C6 --k 7 --min-and 0 --mis-lower --lex --input-budget --seconds 60
python3 single_query.py --help
python3 h12_and5_reproducer.py --output h12-and5.smt2 --solve
```

The exact counter tests and small-circuit checks are implementation validation,
not a formal proof of the general synthesis normalization. Independent review
covered the mathematical arguments, CNF clauses, padding, explicit restrictions,
all new fixtures, and execution from a different directory.
