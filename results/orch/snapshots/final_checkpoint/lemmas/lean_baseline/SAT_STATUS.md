This directory preserves Lean baseline components and SAT construction research for L-meta-650. No exact full 26-input circuit with at most 63 gates has been found by this lane.

The exact full graph has 52 edges. Its checked standard circuit uses 64 gates. The generated filtered phase bank contains 156 exact 66-gate/14-AND full circuits. The six-owner bank contains 72 exact 31-gate/7-AND circuits; completing a correct core of at most 28 gates would give a full 63-gate circuit.

The finite computational exclusions below are not Lean kernel theorems about the posted task. Their exact DIMACS formulae and solver proofs are preserved, and the stated LRAT certificates were accepted by an independent bundled Lean runtime checker. The runtime checker used no native_decide.

| Model | Outcome | Preserved certificate |
|---|---|---|
| Five-owner raw 16 graph, 5 AND nodes, arbitrary OR subsets, empty OR=false, dirty independent support at most2, no optional minimality/Kraft cuts | UNSAT; independent LRAT runtime check accepted | sat/and_archive/dirty5_uncut_unsat |
| Same five-owner model with positive-live ANDs, negative-child incomparability, allowed dirty-pair family and full equal-child Kraft slack 2 | UNSAT; independent LRAT runtime check accepted | sat/and_archive/dirty5_strengthened_unsat |
| Six-owner raw 17 graph, 6 AND nodes, arbitrary OR subsets, positive-live ANDs, negative-child incomparability and full equal-child Kraft slack 12 | UNSAT; independent LRAT runtime check accepted | sat/and_archive/dirty6_strengthened_unsat |
| Six-owner6-AND uncut model | UNKNOWN after 1200 seconds | sat/and_archive/dirty6_uncut_1200s |
| Full26-input13-AND uncut model | UNKNOWN after 1200 seconds | sat/and_archive/dirty13_uncut_1200s |
| Full13-AND model with reviewed dirty-pair orbits and minimality cuts | UNKNOWN after 1200 seconds | sat/and_archive/dirty13_orbit_minimal_1200s |

The AND-subset abstraction has no constant-true atom, and ignores ordinary OR-gate cost unless an explicit construction budget is enabled. An exact abstract model alone is not a63-gate witness. All later budget models assemble actual binary AND/OR circuits and verify the complete raw truth table before publishing a target witness.

The joint six-owner packet supplies 17 raw inputs and 25 correlated outside OR prefixes. Using at most one optional pair per outside owner permits a28-gate core to attach with 35 additional gates. A seven-AND separate-cone construction costs T−8, where T counts all selected source occurrences and every cone is nonempty. With one paid shared OR, the exact cost is T−9. The positioned variant allows that shared OR to read earlier AND outputs and forbids all backward references.

The optional seven-AND Kraft constraint counts equal children, including both00 and11, on all 52 maximal negatives. It enforces total weight at most 128, equivalently excess charge at most 76. The optional all-live clauses are explicitly a construction-profile restriction: every AND and the shared OR must have a path to the output. No necessity claim at seven ANDs is made for that profile.

Completed searches and current/final statuses are recorded in each archive status.json and full solver.log. Local selector-radius exclusions refer only to those neighborhoods; interrupted remainders are separately labeled and are never counted as solver UNKNOWN or UNSAT outcomes.

Final active models use and_skeleton_shared_or.py, and_skeleton_shared_or_position.py and the independently reviewed and_skeleton_kraft.py. Their archives include frozen launch sources, exact formulae, phases, model specifications, input/source hashes and lease-receipt filenames. Calibration logs beside the sources include full truth-table checks, cost checks, signed arithmetic fixtures and disabled-model identity checks.

Snapshot UTC: 2026-11-25T07:32:09.613853+00:00

A remaining model limitation is that every free outside prefix is a fixed OR of raw line inputs. Allowing a paid shared OR to read earlier ANDs inside the core does not represent outside prefix trees that incorporate a paid intermediate signal. Algebra_strategy proposed a conditional marker family of that kind near the end of the job; it has not been implemented or established as a63-gate construction by this lane.
Dynamic outside prefixes are not automatically free or correct: adding a marker to an outside guard must preserve the full graph function. A restricted two-owner truth table cannot establish that condition; actual gate accounting and complete global semantics must be checked.

Final update2026-11-25T07:49Z: both final all-live/Kraft target28 searches completed two300-second UNKNOWN intervals with exit0. No exact full63-gate witness was found. Complete final replay data and logs are preserved in and7-final-live-after2 and and7-final-live-after0. Earlier killed intervals are explicitly marked as environment interruptions.
