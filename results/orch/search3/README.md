# L-meta-1772: longer finite searches and shared-factor diagnostics

This archive preserves finite research for the held step. None of the larger
target searches produced a counterexample or a lower-bound certificate.
Diagnostic circuits above the known upper bounds do not refute the statement.

## Target searches

- The initial stress-graph size12 searches, with and without optional local
  minimum pruning, and Petersen size19 search were interrupted by the execution
  environment reset. Their full available stdout/stderr, formulas and metadata
  are retained. `long-search-interruption.json` records the interruption; these
  runs are UNKNOWN, not UNSAT.
- Restarted Petersen size19 ran for 600 seconds and returned UNKNOWN. The
  graph has a clean 20-gate upper bound. The search used the checked group of
  120 vertex automorphisms and orbit restrictions on its first three gates.
- Restarted stress-graph size12 searches, both without and with optional local
  minimum pruning, each ran1200 seconds and returned UNKNOWN. The stress graph
  has eight vertices and ten edges, and a Lean-checked clean13-gate witness in
  `../lemmas/StressGraph.lean`.

The finite stress-graph automorphisms are separately checked in
`../lemmas/StressSymmetry.lean`. This does not formally verify the generic SAT
translation, gate-order normalization, or circuit symmetry restriction.

## Shared-factor diagnostics

`circuit-sat-shared.py` adds optional constraints to the earlier encoder:

- `--shared-or-witness`: an unowned AND has an OR ancestor that also directly
  feeds an AND incomparable with the selected AND in the dependency order;
- `--nonstar-unowned`: the selected unowned AND accepts two disjoint graph edges;
- `--pivotal-gates`: forcing each gate's output to false loses some graph edge.

The first two flags deliberately restrict diagnostic models. They are never
assumed to hold in a minimum circuit. For pivotality, the mathematical necessary
condition for every gate of a minimum graph-function circuit is proved by
`lean/PEqualNP/Outside/L_meta_2668.lean`, lemma `lost_edge`, lines395–430. That
proof deletes the gate and redirects it to an absent false wire. The encoder
uses the equivalent in-place forced-false evaluation; the CNF implementation
was independently reviewed at the hashes in `pivotal-source-review.json`.
All other normalizations remain separate from that Lean theorem.

SAT models are independently checked on every Boolean input, with exact
dependency-cone ownership and, when requested, every gate's pivotal witnesses.

- C5 size8 has nonminimum unowned-AND witnesses, including singleton-safe and
  shared-factor variants. C6 size9 with the requested shared-factor shape was
  UNSAT in that restricted normalized model.
- C5 size9 has a pivotal shared-factor witness whose unowned AND accepts the
  path edges01,12,23, with two different AND ancestors covering those labels.
  All its ANDs reject singleton inputs. Its shared OR03 also feeds the separate
  star04,34. Routing an existing guard into the dirty star removes two gates,
  giving the known seven-gate upper bound.
- C6 size10 has a pivotal shared-factor witness whose unowned AND accepts the
  matching05,23. Two OR factors of its matching filter are shared with outside
  stars. Replacing the private matching block saves one gate; the known global
  upper bound is eight. One earlier AND in this diagnostic fires on singleton0.
- A C5 size7 calibration with pivotal constraints and automorphism-prefix
  restrictions is SAT and independently validates all32 inputs and all seven
  pivotal witnesses.

`validate-models.py` independently rechecks the six SAT models in this archive;
its full truth-table, ownership, shared-factor and pivotality checks all pass.

## Joint-pivotal repair diagnostics

`joint-pivotal-scan.py` enumerates every proper subset S of at most six gates
containing a bad AND in the five nonminimum witnesses. It computes the graph H
of edges lost when every gate in S is simultaneously forced false, and finds a
minimum vertex cover of H by exhaustive enumeration. The clean star-circuit
upper bound is |E(H)|+τ(H)−1 for nonempty H (one false gate for empty H).

Every bad AND in these five witnesses has a class satisfying that budget≤|S|.
Minimum class sizes are4 for the initial C5 eight-gate witness,1 for each of the
two singleton-safe C5 eight-gate witnesses,4 for the pivotal C5 nine-gate
witness, and3 for the pivotal C6 ten-gate witness. These are finite diagnostics
for a proposed repair lemma, not a proof that such classes always exist.
The all-owned C5 calibration has no bad AND and is skipped. Complete subset
counts and up to12 smallest certificates per bad gate are preserved.

## Interpretation and replay

CaDiCaL return10 is SAT, return20 UNSAT, and return0 here is a time-limit UNKNOWN.
No UNSAT result in this archive is a Lean lower-bound certificate. Optional
`--minimal-pruning` excludes locally dominated operand signatures; its
necessary-minimum argument has not been checked in Lean. Its results must stay
separate from searches without that option. Minimum-circuit necessary conditions
at exactly k gates do not rule out a smaller minimum: every relevant smaller
size would also need checking before claiming a lower bound.

Every included completed solver run has its complete stdout/stderr in the
corresponding `-solver.log`, plus the exact CNF and encoding metadata. Initial
interrupted runs retain all output that existed when their processes vanished.
Wrapper `.log` files preserve the command's full stdout/stderr.

The scripts record the original job scratch path. The SAT encoder also accepts
`PNP_SEARCH_DIR` and `PNP_CADICAL` environment variables for replay; the symmetry
wrappers use their explicit `ROOT` and `SOLVER` constants. The executable was
CaDiCaL rel-3.1.0 built from its official GitHub source. It is not in this archive.
The symmetry wrappers invoke the encoder in emit-only mode, add group-orbit
clauses, run the solver with `-t`, and independently validate every SAT witness.
`replay-commands.json` preserves all requested formula flags, including the
experimental flags omitted from some encoding metadata. Its diagnostic time
caps are explicitly replay caps, not asserted original timing records.
