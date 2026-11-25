# L-meta-2583 bounded exact synthesis

The target is size-preserving read-1 normalization for projective-plane
incidence functions computed by binary AND/OR circuits.  Read-1 is per prime
implicant, not a global read-once condition on the DAG.

The order-two case is unsuitable for refutation: the checked repository file
`L_meta_971.lean` proves the unrestricted 27-gate lower bound for the Heawood
function.  For order three the star construction has 64 gates: 52 incidences
plus 13 stars minus one.  The checked read-1 lower bound in `L_meta_7639.lean`
applies to squarefree bipartite incidence with a perfect matching, so a 63-gate
order-three AND/OR circuit would be a possible route to refutation.  No such
circuit is claimed here.

`repair.cpp` performs incremental SAT synthesis in a bounded gate-edit
neighborhood of a numbered seed circuit.  A changed gate may alter its
operation and/or either fanin.  Inputs and output index are fixed.  Fanins
must refer to earlier wires, and AND/OR commutativity sorts the two fanins.
Duplicate fanins and unused gates are allowed.  There is no canonical gate
reordering or graph-automorphism restriction.  An UNSAT result applies only
to this fixed seed, gate numbering, output, and edit radius.

The complete monotone test basis is generated independently by
`../2583-search/plane3.py`: 52 minimal true assignments (incidence edges)
and 704 maximal false assignments.  Every true assignment contains an edge.
For every false assignment with point set A, take all lines disjoint from A
and then all points avoiding those lines.  This extends the assignment to a
maximal false assignment enumerated by the generator.  Thus any monotone
circuit agreeing on all 756 rows agrees on all 2^26 inputs.  The SAT driver
checks the entire supplied basis before writing `WITNESS.json`.

`prepare.py` converts a plane JSON and a seed JSON into the simple text input
for the solver.  The solver uses the already installed CaDiCaL 2.1.2 library;
no new solver was downloaded or built.  Its header is preserved in the
earlier `../exact/` artifacts.  Full stdout/stderr is captured in each log.

Controls:

* `control64.log`: the fixed 64-gate star circuit satisfies all 756 rows.
  SAT and full basis validation took 1.01309 wall / 1.00824 CPU seconds.
* `control63-negative.log`: fixing the 63-gate seed obtained by deleting one
  OR gate is UNSAT on the full basis.  It misses exactly one incidence edge.
  This negative control took 0.759682 wall / 0.761138 CPU seconds.

The status-review agent independently reviewed the new selector, edit-count,
change-indicator, gate-semantics, and validation code before long searches.
No Lean proof or Lean-checked refutation is produced by these experiments.

Bounded-repair results:

* Radius four around the deleted-edge 63-gate seed: UNKNOWN after
  120.021 wall / 92.4759 CPU seconds.  Eight provisional models were checked;
  none passed the complete basis.
* Radius six, preloading all 52 true edges and eight false boundary rows:
  UNKNOWN after 300.001 wall / 262.804 CPU seconds.  Its one provisional model
  accepted all edges but failed 458 maximal false rows.

Five-line local search:

`five_lines.py` classifies all 1,287 five-line subsets of PG(2,3) up to line
permutation.  The point-neighborhood multiset gives exactly three classes,
represented 117, 702, and 468 times.  `five-line-classes.json` records the
complete classification summaries and representatives.

Points with identical singleton neighborhoods can first be combined by OR.
The three resulting compressed instances have 14, 16, and 16 inputs, with
four, one, and zero outside OR gates.  Seeking 19, 22, and 23 gates for the
compressed functions therefore seeks a 23-gate implementation of the
five-line subfunction, whose ordinary star implementation has 24 gates.
`lift_local.py` adds the prefixes and the other eight line stars, yielding
63 full-plane gates from any successful local candidate.  Each of the three
known local star baselines has passed this grafting code and all 756 global
boundary checks, yielding 64-gate positive controls.

`small_nested.py` encodes these finite monotone functions using their edge
assignments and maximal false assignments obtained from all subsets of the
five line variables.  After SAT it separately checks every one of the 2^n
assignments with bit-parallel truth tables.  The strict-saving runs use
`--allow-flat`, so they impose no nested-AND requirement.  Duplicate fanins
are allowed.  The all-active and canonical gate-order conditions do not
exclude smaller circuits: remove unused gates, pad the output with AND
identity gates to the target size, and canonically order the resulting DAG.
UNSAT would still concern this fixed OR-prefix construction, unless the
necessity of the prefix grouping is separately established.

An optional, not-yet-independently-reviewed `--first-orbits` cut restricts the first gate's input pair to the
least pair in its graph-automorphism orbit, measured by (max fanin,min fanin).
It is used only for unseeded synthesis.  It is not applied to numbered
gate-edit neighborhoods.  Full solver logs, generated CNFs, and candidate
circuits are kept in the corresponding run directories.

The lease-loss stop was received during the first five-line search.  Its
Kissat process (PID 19728) was sent SIGINT at 2026-11-25 15:06:35.796 UTC and
exited with signal status -2 after 249.67 CPU seconds.  No SAT model or UNSAT
result was obtained.  The other two five-line searches were never launched,
and the optional first-orbit cut was never used.  No solver remains running
from this agent.  `STOP-lease-loss.json` records the verified process argv and
termination.  All current artifacts are preserved; no further gap work was
performed after the stop, apart from recording final status.
