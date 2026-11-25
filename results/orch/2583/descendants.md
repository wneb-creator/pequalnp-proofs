# L-meta-2583: reusable checked descendants

Updated 2026-11-25, by the descendants agent. No desk or git actions performed.

## Goal and exact obstacle

The lease asks for no-larger Read1 normalization of an arbitrary AO2 circuit
computing the incidence function of a projective plane. Read1 is a condition on
proof trees for each prime implicant: it is not a restriction on global fanout.

The following closed checked theorems show that the goal is equivalent to an
exact unrestricted monotone lower bound of `N * (q + 2) - 1`, once the routine
plane regularity and matching facts are supplied:

* `lean/PEqualNP/Outside/L_meta_7684.lean` (1126 lines) constructs an AO2 Read1
  circuit for any bipartite graph `E` and vertex cover `A,B`, with size at most
  `E.card + A.card + B.card - 1`. For a projective plane choose all points and
  no lines. Its statement is closed, without an unproved leading charge premise.
* `lean/PEqualNP/Outside/L_meta_7639.lean` (1977 lines) gives
  `E.card + N <= C.size + 1` for a C4-free bipartite graph with a perfect
  matching, when C is Read1. This is the matching-specialized form of the next
  result.
* `lean/PEqualNP/Outside/L_meta_4897.lean` (1961 lines) gives a vertex cover
  `A,B` satisfying `E.card + A.card + B.card <= C.size + 1` for a Read1
  circuit computing a C4-free bipartite graph.

These supply construction and Read1 lower bound, but no closed checked
unrestricted exact lower bound was found in the repository census.

## Additional closed routes

* `L_meta_7241.lean` (943 lines): for a C4-free simple graph and an AO2 circuit
  computing it, obtains a vertex cover T with
  `G.edgeFinset.card + T.card <= C.size + 1`, provided **every AND gate rejects
  every nonedge pair input**. This condition is stronger than correctness of
  the output and is not automatically available.
* `L_meta_4543.lean` (1150 lines): gives a no-larger size-minimal `TopForm`
  circuit and minimizes `Ustar` among size-minimal TopForm circuits.
* `L_meta_8899.lean` (696 lines): gives a no-larger incidence circuit in which
  no AND gate that rejects all specified false inputs is below another AND.
  It preserves correctness on incident pairs and false inputs with bounded
  line support. It does not assert that all AND gates are sound.
* `L_meta_4990.lean` (939 lines): closed exact cover lower bound for circuits
  with separate pure OR wire sets for the two variable sides and every AND
  taking an input from each side.
* `L_meta_6579.lean` (378 lines), also embedded in L7684: such separate-side
  OR/AND circuits are Read1. This proof establishes a unit-vector read witness
  on a true pure wire, then combines opposite-side unit vectors at an AND.

Possible missing route: prove projective-plane minimal TopForm circuits admit
all-AND nonedge-pair-sound normalization; L7241 then gives the required exact
budget. This is a new proof obligation, not an established implication.

## Existing reductions and non-solutions

* `R_meta_4895_1.lean` (32 lines) reduces generic C4-free no-larger Read1
  normalization to an unrestricted exact cover budget and the Read1 star
  builder. The builder is now solved by L7684; the budget is the whole hard
  part.
* `R_meta_4895_215.lean` (126 lines) and `R_meta_4895_628.lean` (329 lines)
  replace the cover budget by the matching charge
  `E.card + M.card <= C.size + 1`. They prove Konig matching/cover duality
  through `Finset.all_card_le_biUnion_card_iff_existsInjective'`.
* `L_meta_7344.lean` (399 lines) repairs a quadratic monotone circuit to Read1
  with multiplicative/additive overhead involving the number of failed Read1
  prime implicants. It does not give a no-larger circuit.
* `L_meta_1955.lean` (189 lines) **is not a closed lower bound**. Its main
  theorem starts with two large universal premises for charge and structural
  decomposition. Merely inspecting the end of its statement is misleading.
  The following helper lemmas inside it are unconditional and reusable:
  `lines_through` at lines 6-42 gives point degree q+1;
  `cover` at lines 58-86 gives `N <= A.card + B.card` from regularity;
  `count` at lines 88-132 is a finite double-counting estimate.
  These helpers were reported to lower_bound, who owns plane combinatorics.

## Local census artifacts

All in `/tmp/oec/pequalnp-pilot-118/`:

* `descendants2583-readk-statements.json`: Read1-related theorem signatures.
* `descendants2583-plane-statements.json`: 83 incidence/unique-line theorem
  signatures. Earlier extraction split on the first `:=` and can truncate
  statements containing internal lets; use sources for exact claims.
* `descendants2583-ao2-card-statements.json`: 49 bounded-size AO2/cardinality
  theorem signatures, extracted up to `:= by` to preserve internal lets.

Only full signatures were used to identify the closed theorems above. Existing
`L_` filenames do not guarantee an unconditional theorem: some retain leading
universal hypotheses.

## Previous lease preservation

The old L-meta-2592 ProjectionStandalone process (PID 5981) was terminated
safely after the parent pushed all old source/logs as commit `3415fbc0`. Its
expensive kernel certificate had not finished. No claim of a compiled
projection proof is made.
