This is exploratory SMT evidence, not a Lean certificate.

The full-semantics synthesizer encodes every Boolean assignment as one bit of a
bitvector. An input variable has its exact truth table; every gate has two
selected earlier wires and operation AND, OR, or NOT of its first input.
The active gates form a prefix of length `used`, bounded by the requested gate
budget. At most one active NOT is allowed. Every requested OR target must equal
an active gate truth table. The tables include all assignments, not only
singletons. Generated SMT-LIB is preserved in each `.smt2` file.

Normalization and relaxations:

* False and true constants are available free. False simulates a nonexistent
  index in the Lean evaluator. Free true strengthens the search model: a SAT
  result using it may need an additional actual gate and must be revalidated;
  UNSAT remains a valid lower-bound result for that fixed family.
* Binary gates can repeat inputs, simulating unary AND/OR. Zero-input gates
  evaluate to free constants. A NOT with no inputs is constant true; otherwise
  only its first input matters. Thus the unusual Lean arity semantics are
  covered.
* Future and nonexistent indices always read false at the gate that uses them;
  replacing these reads by the free false wire preserves all truth tables.
* Commutative inputs are ordered; NOT uses equal dummy input indices. These
  changes do not restrict the computed function.
* Active gate functions are distinct from earlier wires, input variables, and
  constants. Any circuit can be reduced to this form by replacing duplicate
  wires with their earlier equivalents and deleting the duplicate gates.
* Every active gate is a requested output or is read by a later active gate.
  Iterated deletion of unused gates gives this property without changing any
  requested output or increasing the number of NOTs.
* Inactive gates are fixed to a repeated-input AND and cannot be chosen as
  outputs or predecessors of active gates. Hence the queries cover at most
  the budget, not merely exactly the budget.

The positive-control Pasch query found eight ordinary OR gates; its inputs do
not use either free constant. The corresponding seven-gate query returned
UNSAT. The initial `pasch7` query used exactly seven reduced gates; rely on
`pasch_le7` for the at-most-seven result instead.

The singleton mode is a separate, deliberately weaker abstraction: each bit
represents one singleton input, and NOT is forbidden. Its results must never
be confused with full circuit semantics.

The `good` mode tests a proposed ownership lemma, not the posted theorem.
That lemma has a hand-constructed ten-gate counterexample in
`good_count_counterexample.py`; all 32 input assignments were checked.

Search status:

* `pasch_le7`: UNSAT, 32.841 seconds.
* `pasch_le8`: SAT, 14.819 seconds, ordinary eight-OR-gate positive control.
* `pasch_singleton_le7`: UNSAT, 9.434 seconds, singleton abstraction only.
* `fano5_le9`: UNKNOWN after 300 seconds; no conclusion.
* `fano_le13`: terminated without a solver result after a mathematical proof
  route for all size-three targets made this search redundant.
* `or4_atmost2good`: terminated without a solver result after the explicit
  ten-gate counterexample refuted the proposed unbounded ownership lemma.

No counterexample to L-meta-951 has been found.

Additional completed full-semantics results:

| Family | Posted-style bound | Budget checked | Result |
| --- | ---: | ---: | --- |
| 0123, 0456, 14, 25 | 8 | 7 | UNSAT, 142.420 s |
| 01234, 056, 157 | 8 | 7 | UNSAT with qffd, 103.570 s |
| 0123, 0456, 14, 25, 36 | 9 | 8 | UNSAT with pure bitvectors, 83.840 s |
| 0123, 0456, 14, 25 | 8 | 8, exactly one NOT | UNSAT, 94.987 s |
| K5 edge-star family | 15 | 14 | UNKNOWN after 601 s |
| K5 edge-star family, first gate NOT(input 0) | 15 | 14 | UNKNOWN after 180 s |
| K5-minus-one-edge star family | 13 | 12 | UNKNOWN after 300 s |
| 0123, 0456, 14, 25, 36 | 9 | 9, exactly one NOT | UNKNOWN after 180 s |

Digits in a family cell denote distinct input-variable indices. All of these
families have pairwise intersections of size at most one. The K5 family is
0123, 0456, 1478, 2579, 3689; K5-minus-edge is
0123, 0456, 1478, 257, 368.

The pure-bitvector engine `bv_synthesize.py` independently encodes selectors,
operations, and active-prefix length using bounded bitvectors, and enforces
the NOT limit with pairwise Boolean clauses. It returned SAT for the ordinary
eight-gate Pasch circuit in 0.995 s and UNSAT below eight in 9.862 s. Every SAT
model is reevaluated over the entire Boolean cube by Python before reporting
`VALID_FULL_CIRCUIT`. The encoding still has free constants, which are flagged
in any model. All positive controls used no free constants.

The CEGIS engine `cegis.py` starts with zero, all singleton inputs, every
outside-of-target input, and the all-ones input. It validates a candidate on
the full Boolean cube and adds failing inputs before continuing. It does not
impose distinct-function constraints on partial truth tables: doing so would
be unsound. It charges one gate for a true constant, while false is free as
in the Lean model. An UNSAT answer on a subset of assignments is a sound
finite-family lower bound; a SAT answer becomes a full circuit result only
after all assignments pass its independent validation.

The initial CEGIS query for family 0123, 0456, 14, 25 at budget seven was UNSAT
on just its thirteen selected assignments in 77.885 s. The all-ones row is an
extra assumption compared with the proposed zero/singleton/outside-only
abstraction, so this result does not establish that exact weaker abstraction.
The K5 initial CEGIS query timed out at 180 s without a candidate.

`conditional.py` explores a separate proposed proof lemma, not the posted
theorem: monotone outputs Gi satisfy Gi <= OR(Si) and h AND OR(Si) <= Gi,
and h is true outside every target. It counts the circuitry computing h.
Its small mixed-family query timed out at 180 s. That proposed general lemma
was subsequently refuted algebraically by another agent's two-copy
projective-plane construction, independently checked here. No further
conditional queries are running.

All solver processes in the initial report had terminated. UNKNOWN and
terminated runs are not evidence that a counterexample is absent.

Continued work, 2026-11-23:

* The K5 zero-NOT baseline was kernel checked in `K5Monotone.lean`, using the
  existing theorem L_meta_924. Both the module build and scratch Lean check
  exited zero.
* A delegated independent proof in `literal-not/K5LiteralNot.lean` was kernel
  checked. It proves at least fifteen gates for K5 whenever the sole NOT reads
  any original input, at any position. Its reusable constant-folding theorem
  is in `literal-not/CountedRestriction.lean` (only Mathlib and Defs). This
  settles the NOT-first branch of the search partition independently of SAT.
* The first-gate partition is AND/OR on adjacent K5 edges, AND/OR on disjoint
  K5 edges, and NOT of one edge input. The K5 automorphism group is transitive
  on each of these types. Constants and unary/repeated AND/OR gates can be
  folded away before taking the first gate.
* Adjacent independent gates after the fixed first gate are ordered
  lexicographically by their operation and operand indices. This is sound:
  choose a lexicographically minimal topological ordering with gate zero
  fixed. Swapping an independent adjacent inversion leaves both gates' operand
  indices unchanged and lowers the sequence; later references are renumbered.
  Another agent independently audited this reduction. A Pasch-eight positive
  control passed with this condition.
* AND-adjacent and OR-adjacent K5 cases both returned UNKNOWN after about 903
  seconds. AND-disjoint and OR-disjoint were then started with 900-second
  budgets and exactly one NOT. The checked zero-NOT baseline covers the
  excluded monotone cases. Their final statuses belong in their complete logs.
* Full free-antitone-oracle tests add an arbitrary antitone Boolean truth
  table as a free input and allow only AND/OR gates. Every cube-cover relation
  is imposed. These are stronger relaxations, not the posted circuit model.
  Pasch budget seven was UNSAT (27.729 s); its budget-eight control was SAT
  using ordinary OR gates and no oracle. The old control log's generic
  `this_is_only_a_relaxed_counterexample` label does not mean it violates a
  bound: it uses eight gates, equal to the known bound. Later code records
  `violates_sum_bound` explicitly.
* Free-oracle family 0123,0456,14,25 at budget seven was UNSAT (63.769 s).
  Adding target 36 and using budget eight was UNKNOWN after 180 seconds.
  The wheel family 0123,045,156,267,374 at budget ten was UNKNOWN after 300
  seconds.
* `antitone_cegis.py` verifies every candidate over the full Boolean cube.
  For each input it computes whether oracle zero and/or one can produce the
  target vector. Forced-one inputs generate a downward closure; any forced
  zero inside that closure refutes an antitone extension. Otherwise the
  closure is a complete antitone oracle and every output is checked. Partial
  queries constrain all comparable sampled pairs and use no function-based
  distinctness pruning. Pasch budget eight passed the positive control over
  all 64 assignments; budget seven was UNSAT already on the sampled rows in
  13.481 seconds.

Current snapshot at 2026-11-23 20:43 UTC:

* Both remaining K5 binary first-gate cases ended UNKNOWN: AND-disjoint
  902.695 s and OR-disjoint 902.000 s. Together with the two adjacent cases,
  the four computational branches are inconclusive. Only the literal-NOT
  branch has the independent Lean certificate described above.
* Family 02,03,0456,14,15,1236 has target sum 10. The unrestricted full-table
  query with at most nine gates and at most one NOT returned UNSAT in
  347.042 s. It covers all 128 assignments and does not assume Good ownership.
  Files: partial_grid7_full9.log and its generated query.
* Two exploratory queries are still running at this snapshot: the nine-input
  family 02,0345,0678,136,147,1258 at budget 13 (target sum 14), and a free
  antitone-oracle relaxation of the preceding seven-input family at budget
  nine. A running query supplies no result.
* The nine-input query uses `ownership`: every target must own at least
  min(cardinality minus one, two) Good gates. This follows the separately
  proved ownership lemmas, but is an additional mathematical prerequisite
  compared with an unpruned solver query. The `tightgood` mode encodes the
  special equality case and was not used for any claimed result here.

No posted-statement counterexample or full universal proof has been found.
Diagnostic counterexamples to proposed helper lemmas are not refutations of
L-meta-951. UNKNOWN, canceled, and running cases provide no lower bound.
