# L-meta-1772: pivotal normal forms and TopForm search

This archive preserves further finite research. It contains no proof or
refutation of the posted gap. Experimental circuit restrictions and finite
diagnostics are distinguished from checked Lean normalization theorems.

## Target searches

The stress-graph size12 run with all-gate pivotality and optional local signature
pruning was interrupted by the environment refresh around04:43UTC. Its process
was a zombie, its exec session had vanished, and no solver verdict or summary
existed. The full156,500-byte solver log is preserved, with its hash and an
`INTERRUPTED_UNKNOWN` record in `pivotal-search-interruption.json`. Its planned
1200-second limit did not complete.

A fresh600-second Petersen size19 run started04:46UTC with all-gate pivotality,
the joint two-pivot condition, TopForm, depth3 graph-automorphism restrictions,
and separately flagged local signature pruning. It completed600.03 seconds
UNKNOWN, with no witness or lower-bound conclusion. Petersen has a clean20-gate
upper bound.

The composition theorem compiled while that run was in progress:
`IntegratedNormalForm.exists_integrated_normal_form` gives a public minimum
satisfying TopForm and the joint two-pivot condition simultaneously for every
nonempty finite graph. The source hash and complete successful Lean build log
are recorded here, and independent theorem review passed at that hash. The
separate CNF, normalization and symmetry caveats below still apply.

## New optional constraints

- `--unowned-two-pivots`: every AND either owns some graph edge or has at least
  two distinct unordered graph edges lost when its output is forced false.
  `PivotalNormalForm.pivotal_bad_normal_form` proves existence of a minimum with
  this property. It is not asserted of every minimum.
- `--defective-two-pivots`: adds the same two-edge requirement for every unsound
  AND, including those owning an edge. All maximal independent negative inputs
  characterize unsoundness by monotonicity. The checked
  `JointNormalForm.exists_joint_pivotal_normal_form` supplies a minimum with both
  dirty-gate and unowned-gate conditions.
- `--top-form`: no graph-sound AND may be a strict ancestor of another AND.
  Structural reachability and the same maximal-independent tests encode this
  exact predicate. Existing `L_meta_1733` supplies TopForm at the same size and
  dirty count in the strict binary model. Composition with the preceding
  condition is supplied by the new integrated theorem for nonempty graphs.

Each source implementation was independently reviewed. Every SAT witness is
checked on all Boolean inputs, with exact dependency cones, ownership, dirty
ANDs, forced-false pivotal witnesses, and TopForm when requested. The archive's
`validate-models.py` separately repeats those checks.

Pinned-model regressions preserve complete formulas and solver output:

- An unowned one-pivot C5 model is SAT in the pivotal control and UNSAT with
  `--unowned-two-pivots`; a three-pivot unowned model remains SAT.
- A six-gate triangle model has an owned unsound AND with one pivotal edge and
  a different unowned AND with three. It is SAT with the preceding flag and
  UNSAT with `--defective-two-pivots`. This deliberately nonminimum triangle
  example is outside the target graph class and tests the encoder only.
- A seven-gate C5 model with a sound AND ancestor is SAT without TopForm and
  UNSAT with it, while a clean seven-gate model remains SAT.
- C5 seven-gate calibrations pass with each successive combined restriction.

## Additional diagnostics

The pure-OR locality search finds a C5 seven-gate model where OR(1,3) is pivotal
on edge34 although1 is not adjacent4. All its ANDs are sound and own edges, but
it violates TopForm. A same-size clean rearrangement is available. This warns
against deducing the proposed locality property from minimum size alone;
minimality of the displayed circuit is not proved in Lean by this archive.
The corresponding C6 eight-gate restricted normalized search is UNSAT in9.94s.
A C7 ten-gate search with TopForm and the same requested locality violation
reaches its60-second limit UNKNOWN. None of these results addresses the
existential target statement.

`joint-unsound-scan.py` checks every proper set of at most six gates containing
each unsound AND in the five earlier nonminimum diagnostics. All six unsound
gates have a class whose jointly lost-edge graph H admits a clean star circuit
within the removed-gate budget. Minimum class sizes are4,1,1,2,3,3. Full subset
counts and certificates are saved. This is not a universal repair theorem.

The algebraic-route files `alg-fivefactor-star.*` and
`alg-fivefactor-topform.*` preserve a separate closure obstruction on K1,3
disjoint C5. Five factors together give a sound centered filter whose accepted
graph edges form a star, while every proper subproduct remains unsound. The
filter also accepts the center together with both endpoints of a cycle edge.
The explicit32-gate full-graph circuit is validated
on all512 inputs, including cones, soundness, ownership and TopForm. It is
deliberately nonminimum and provides no circuit-size separation.

## Scope and replay

SAT is return10, UNSAT return20, and time-limit UNKNOWN return0. The base SAT
translation, gate-order normalization and automorphism restrictions are not
Lean certificates. Optional local signature pruning has an informal
necessary-minimum argument. Excluding exactly k gates under conditions on a
minimum does not exclude a smaller minimum without checking smaller sizes too.

Complete stdout/stderr, exact CNFs and metadata are retained. Pinned-regression
generators and validation reports record which controls must be SAT or UNSAT.
Some repeated small model JSON files are dependencies copied from search3.
The joint-unsound scan also references that earlier archive's six-model index.
Scripts use the original scratch path; the base encoders accept
`PNP_SEARCH_DIR` and `PNP_CADICAL`, while symmetry wrappers expose explicit
`ROOT` and `SOLVER` constants. CaDiCaL rel-3.1.0 is required for replay and is
not included here. No solver result here is a Lean lower-bound certificate.
