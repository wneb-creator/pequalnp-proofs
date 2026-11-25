# Bounded-AND / free-OR searches for L-meta-2448

These are exploratory computations, not a Lean proof of L-meta-2448.
The search bounds the number of AND gates while allowing arbitrary OR gates.
The posted gap concerns minimum **total** circuit size and star ownership;
none of the normalizations below preserves the number of OR gates.
UNSAT is a SAT solver result for the saved encoding, not a kernel-checked theorem.
UNKNOWN means the solver reached its time limit without a SAT/UNSAT result.

## Preserved artifacts

`catalog.json` maps every run to its exact source, source SHA256, graph,
AND-slot count, mode, dual flag, observed status and wall-time limit.
For every run, `runs/` contains the complete generated DIMACS CNF, complete
solver stdout and stderr (`.solver.log`), complete runner stdout and stderr
(`-run.log`), and parsed metadata (`.json`). SAT models appear both in the
complete solver log and as reconstructed source choices in the JSON.
No solver binaries are included.

The six scripts in `sources/` are frozen copies of the exploratory sources.
They use the original container's absolute CaDiCaL executable path. To repeat
a run in another environment, adjust only that executable path, then use
the graph, AND count, dual flag, time limit and a new output prefix recorded
in `catalog.json`. Do not overwrite the frozen runs.

`SHA256SUMS` covers every other file in this directory recursively. Paths are
relative to this directory. The manifest itself is not self-hashed.

## Encoding and scope

Each of at most k AND nodes receives two ORs of selected primary variables
and earlier AND nodes. The final output is an OR of selected AND nodes.
Empty ORs represent false, and unused slots may be false. Constant-true
subcircuits and aliases can be removed before this representation without
increasing the AND count. No primary variable is required as a final output
term because the targets used here reject every singleton input.

For the graph edge function, the critical rows are all edge-pair inputs
(positive) and all maximal independent sets (negative). Monotonicity makes
these rows sufficient for full functional equality. Tseitin clauses encode
the selector/value conjunctions, operand ORs, AND nodes and final output.
The scripts check complete SAT models against every generated clause and
evaluate the reconstructed circuit on every one of the 2^n inputs.
The binary circuits in SAT JSON files are explicit AND/OR realizations,
with semantic caching and unused gates removed; their sizes are upper
bounds, not claims of minimum total size.

The variants add the following constraints:

- `base`: no additional source restrictions.
- `disjoint`: an AND's left and right source sets are disjoint. This is
  complete for AND count: represent each old wire as an OR of normalized
  sources, extract the intersection S of two operand source sets, and use
  `(S or A) and (S or B) = S or (A and B)` on the disjoint differences.
  At most one new AND node is needed per old AND node.
- `disjoint_ordered`: also require the smallest selected source to be on
  the left. Swap nonempty disjoint operands to achieve this; if an operand
  is empty, the node is false and both operands can be empty.
- `top`: also select exactly all semantically clean AND nodes at the
  output, and prohibit their use in later AND nodes. A clean node is false
  on every negative critical row, equivalently below the target function.
  Process nodes in ascending order. Expose each currently clean node at
  the output and remove its source occurrences from later operand ORs.
  When that node is false, evaluation is unchanged; when it is true, the
  exposed output already accepts. Later values only decrease. Reorient
  operand sides after deletion if needed. This establishes completeness
  for AND count, with ORs free.
- `dual`: complement every critical input and flip its target bit, giving
  `Fd(x) = not F(not x)`. An AND-count statement for this dual corresponds
  to an OR-count statement for the original function. The dual script
  explicitly checks singleton silence before omitting primary output
  terms. All dual targets in this snapshot pass that check.

The base-dual source gained its singleton-silence assertion after the three
base-dual runs had started. The assertion changes no generated clauses for
these graphs; independent reconstruction verified exact CNF equality.
The frozen top-dual source had the assertion from the outset.

## Results

Times below are elapsed solver seconds. AND counts in dual rows are ANDs
of the dual function, hence ORs of the original function.

| Run | Mode | Slots | Result | Seconds |
| --- | --- | ---: | --- | ---: |
| c7-and3 | base | 3 | UNSAT | 0.134 |
| c7-and4 | base | 4 | SAT | 0.046 |
| petersen-and5 | base | 5 | UNKNOWN | 120.014 |
| c5-or3 | base, dual | 3 | UNSAT | 0.075 |
| c5-or4 | base, dual | 4 | SAT | 0.018 |
| c7-or5 | base, dual | 5 | UNSAT | 23.699 |
| c7-disjoint-and4 | disjoint | 4 | SAT | 0.008 |
| petersen-disjoint-and5 | disjoint | 5 | UNKNOWN | 120.007 |
| c9-disjoint-ordered-and4 | disjoint, ordered | 4 | UNSAT | 0.492 |
| petersen-disjoint-ordered-and5 | disjoint, ordered | 5 | UNSAT | 142.075 |
| c7-top-and4 | top | 4 | SAT | 0.023 |
| petersen-top-and5 | top | 5 | UNSAT | 114.538 |
| petersen-top-and6 | top | 6 | SAT | 0.225 |
| petersen-top-or13 | top, dual | 13 | UNKNOWN | 120.036 |

The Petersen five-AND UNSAT result does not need the optional top
constraints: the disjoint-and-ordered run independently obtained UNSAT.
The six-AND Petersen calibration uses top mode; its concrete realization
has 24 binary gates and passed all 1,024 inputs. This is not a claim that
24 is the minimum total size.

The C7 top-mode four-AND witness has 14 binary gates and includes an AND
owning a nonstar set of edges. It is not a counterexample to L-meta-2448:
the circuit is not of minimum total size. It shows why minimizing the AND
count alone cannot justify a star-ownership conclusion for that circuit.

## Independent review

The `lean_setup` agent reviewed the base encoder, then independently
reconstructed all 14 saved CNFs clause-for-clause from a separate generator.
Every generated CNF matched its run/source mapping exactly. The reviewer
checked all five saved SAT models against their CNFs and checked both the
collapsed and binary circuits on every input. All checks passed, including
the Petersen six-AND witness on all 1,024 inputs.
The separate [review script](../free_or_review.py) and its complete
[stdout and stderr](../free_or_review.log) are preserved beside this snapshot.

The `status_review` agent independently checked completeness of the
disjoint-and-ordered normalization and the optional clean-output top
normalization. Both passed as AND-count normalizations only. These reviews
do not turn the solver's UNSAT output into a Lean proof or establish a
total-gate lower bound.
