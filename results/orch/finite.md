# Finite-case investigation for L-meta-2448

These are computational investigations, not Lean-checked results; exhaustive cases and heuristic searches are distinguished below.

- For 4 inputs, enumerated semantic AND/OR circuit states through depth 4. All 38 labelled triangle-free, four-cycle-free graphs had a minimum witness with a star profile. State counts by depth: 13, 126, 1102, 9279.
- For 5 inputs, enumerated through depth 5. All 291 labelled forests had a minimum witness with a star profile. State counts: 21, 330, 4750, 67005, 958669.
- The remaining 12 labelled admissible 5-vertex graphs are copies of C5. Every possible extra AND/OR gate from every depth-5 state was checked; none computes a C5 edge function. Thus the computation finds no C5 circuit with at most 6 gates. Standard star-cover circuits have 7 gates.
- A separate scan of every minimum output candidate arising from the chosen canonical state witnesses found no minimum circuit lacking a star profile. This is not exhaustive over ownership profiles, because equal semantic signal sets share one circuit representative.

Method: represent each signal by its full truth table, start with all input signals, and enumerate every new binary AND/OR of available signals plus a nullary AND for true. Constant false is freely available from an out-of-range wire, but gates involving it cannot produce a new useful signal. Duplicate semantic gates and unary gates cannot improve a minimum. State keys are sets of generated truth tables; each state stores one circuit witness. This merging preserves reachability/minimum gate counts, not ownership profiles. The star check uses each gate's ancestor set and tests the literal Owns condition at each graph edge.

Structural obstruction: ownership is not automatically star for arbitrary computing circuits (an irrelevant nullary AND owns every edge). In a minimum circuit, constants, unary aliases, and dead gates should disappear. An AND owning two disjoint edges has a false positive on a singleton/nonedge among the four endpoints, as already proved inside R_meta_2448_263; the unsolved exchange must remove/move such an AND without increasing size. This finite search found no counterexample.

Original scratch copies are under /tmp/oec/pequalnp-pilot-75/finite/; reviewed artifacts are also preserved in results/orch/finite/.

search.py SHA256 a621076064c49e96f7a929fc27c799f7fafe086042defeeeaedf490345ececde

search5.py SHA256 bde2d8cf88f63496dde605b9e66f9cbcaf67970786355fbef4ae720f8d85db11

search5six.py SHA256 5496fef9b054e8417f9c8a84a93417cd7e3e8965dfee0d70617289802368f06d

nonstar5.py SHA256 232b4b122949d162eca06d834828cae5b02206adac0944e3021c867f1d7e52ac

Updated 2026-11-25T07:08:47.241942+00:00

## Larger and profile-directed heuristic searches

The local environment has g++/scipy/numpy but no z3/pysat/ortools. A C++ circuit search uses an exact test reduction for monotone circuits: every graph edge pair must be true, and every maximal independent set must be false. Monotonicity then determines every other assignment. Petersen has 30 critical rows (15+15); Heawood has 58 (21+37), so every signal uses one uint64. Minimum-cover star circuits seed the search; removing one gate supplies near-correct candidates. Target sizes: Petersen19 versus cover20, Heawood26 versus cover27. Both 600-second runs remain in progress as of this note. No exact candidate has been found yet.

Independent profile-directed annealing at the cover size searched for a computing circuit with an AND owning disjoint edges. No such circuit was found for C5 (7 gates, 513.8 million mutations), C6 (8 gates, 877.4 million mutations), or C5+leaf (8 gates, 613.0 million mutations), 120 seconds each. These are heuristic negative observations, not lower bounds or proofs that all minima have star profiles.

A random 7-input DAG census is also running: whenever a generated signal is exactly a pure graph edge function, derive its graph, reject triangles/4-cycles, and compare the useful ancestor cone size with the graph cover bound. A below-bound circuit or an equal-bound circuit with bad ownership will be reported for inspection.

Updated 2026-11-25T07:17:45.210352+00:00

## Completed heuristic results and preserved artifacts

- Petersen,19 gates:4,332,400,000 mutations,21,662 restarts,600.004s; best one failed critical row, no exact witness.
- Heawood,26 gates:3,947,000,000 mutations,19,735 restarts,600.010s; best one failed critical row, no exact witness.
- Random7 census:82,736,023 DAGs,1,043,016,003 generated signals,337,678,872 exact quadratic graph outputs,327,356,158 admissible outputs,297,678,746 useful output cones at or below their cover bound,23,621 distinct admissible graphs encountered;180.001s; no below-bound or bad-profile at-bound witness. This is randomized coverage, not exhaustive over all circuits.
- Shared-pure-OR census:26,966,436 DAGs,339,934,059 signals,110,043,677 quadratic outputs,106,680,756 admissible outputs,97,007,076 at/below-cover useful cones,18,700 distinct admissible graphs;60.002s; no shared pure OR witness. Sharing means two distinct parent gates in the useful output cone, and pure OR is checked on the complete128-entry truth table.
- Canonical BFS minimum-witness scan on all291 five-vertex forests found no shared pure OR signal with at least two singleton supports. Alternate implementations of equal semantic states were not exhausted.

Programs, exact graph files, critical-row files, completed full logs, and a SHA256 manifest are preserved in results/orch/finite/. Sources can be compiled with g++ -O3 -std=c++20; no third-party solver download was used.

Theta targets now running: theta(2,3,3) has vertices0..6 and edges02,03,05,12,14,16,34,56; alpha3, cover number4, cover circuit11, search10. Its exact critical rows are5,9,33,6,18,66,24,96,3,42,44,52,76,81,84. Theta(3,3,3) has vertices0..7 and edges02,04,06,13,15,17,23,45,67; alpha4, cover number4, cover circuit12, search11. Its rows are5,17,65,10,34,130,12,48,192,3,86,88,100,104,148,152,164,169. Each is receiving600s of heuristic search.

A distinct bounded MILP synthesis model is also running on each theta target for300s with HiGHS threads=1. Gate operations, fanin selectors, and all critical-row wire values are binary variables; last-wire outputs are fixed to the graph truth values. The model was validated with a fixed C5 seven-gate cover circuit and its returned circuit independently rechecked on all32 assignments (no failures). Source run1 is preserved because SciPy ignored parallel='off'; threads=1 was accepted. Future source uses parallel=False. A timeout will be reported only as a timeout; numerical solver infeasibility would still not be a Lean proof.

Updated 2026-11-25T07:25:46.035318+00:00

## SAT outcomes and environment interruption

The bundled Lean toolchain includes CaDiCaL. Base synth_sat.py and the shared variant have now passed independent review by lean_setup. The model is exactly K topological binary AND/OR gates, with distinct operands ordered a<b, every primary input mentioned, and last-gate output. It does not directly encode nullary/unary gates, constants, or bad-wire reads. Removing constants, aliases, duplicate signals and unused gates justifies this normalization for minimum circuits of the current nonconstant graphs without isolated vertices; this reduction has not been formalized in Lean here. No depth-sorting restriction was used in the reported SAT runs.

- C5 K=7: SAT in0.115s. Decoded circuit independently verified on all32 input assignments; no failures.
- C5 K=6: UNSAT in0.215s, agreeing with the earlier exhaustive semantic BFS.
- C6 K=7: UNSAT in5.808s.
- C5 K=7 plus a shared pure OR: UNSAT in4.377s. This query checks all32 truth rows, enumerates all subsets of at least2 primary inputs as the possible pure-OR support, requires the selected gate to be OR and used by at least2 distinct later parents, and requires every gate to be in the output ancestor cone. It has also been independently reviewed.
- Theta233 K=10 and Theta333 K=11: UNKNOWN/interrupted by execution-environment refresh, with solver CPU times294s and299s. These were not UNSAT outcomes and did not reach their native900s wall limit.
- C6 K=8 shared pure OR: UNKNOWN/interrupted by the same refresh, solver CPU time55s. No verdict was emitted before interruption.

The old solver processes were observed as zombies (STAT Z), not live searches. Full logs end in progress lines without an s-status. Recovery metadata is saved as sat-recovery-run1.json; no incomplete run has been relabeled timeout or UNSAT. CaDiCaL had native -t limits, independently of vanished Python wrappers.

Theta heuristic600s results:233 used4,805,000,000 mutations and333 used4,432,800,000; best one failed critical row in each, no exact smaller circuit. Both theta MILP300s runs returned time-limit status with no incumbent. Unrestricted C5 ordered-MILP validation also timed out30s; the pinned known-valid reordered seed passed and was checked on all32 assignments.

All78 preserved artifacts are under results/orch/finite/ with hashes in sha256.json, including every full stdout/stderr solver log, model CNF, metadata, program source, graph and critical rows. Solver UNSAT is computational evidence about its encoding; none of these results is a Lean-checked lower-bound theorem.

Updated 2026-11-25T07:43:44.857028+00:00

C6 completed follow-up: attempt2 of K8 shared-pure-OR query returned UNSAT in87.906s. A separate unrestricted K8 base-model run returned SAT in1.045s and its decoded witness passed all64 input assignments. This establishes nonvacuous shared-pure-OR exclusion at the bounded model optimum8, paired with earlier K7 UNSAT. These remain solver observations, not Lean theorems. The9 new full artifacts are added to results/orch/finite/; manifest now covers87 artifacts. New any-fanout variant remains outside the repository pending its independent review.

Updated 2026-11-25T07:54:10.468216+00:00

Stronger bounded circuit-shape query: require any useful gate (AND or OR) to feed at least2 distinct later parents, with every gate in the output ancestor cone. C5 K7 returned UNSAT1.919s; C6 K8 returned UNSAT29.047s. Thus these normalized bounded optimum circuit models force all gate fanouts to1. This is not a general formula-normalization theorem and is not Lean-checked. synth_sat_fanout.py independently reviewed PASS, SHA256 b057272d063218c07e041c8dbb86ead6372f7156756345328860ceaabf9d4ede. The9 artifacts are preserved; manifest now96 files.

Updated 2026-11-25T07:55:23.056902+00:00

Theta unrestricted SAT attempt2 finished normally at the native900s limit with exit0 and no SAT/UNSAT verdict:233 used856.04 CPU seconds/900.00 real seconds;333 used848.86/900.01. Both are UNKNOWN/time-limit, not UNSAT. Full logs and theta-sat-timeouts-r2.json are preserved; manifest now105 files.

Ordered theta attempts are now running under new prefixes. The optional larger-fanin-index nondecreasing cut was independently reviewed complete for the base normalized synthesis: sort useful gates bydepth, then bylargerfaninindex within a depth; parents are alreadyindexed and the largestparent lies at the precedingdepth, so orderingis global. Output remainslast. Unused input0-AND-input1 copies canpad the base model toexactK. This padding argument doesnot apply to shared/fanout variants requiring everygate useful; no ordered usefulvariant is being run.

Updated 2026-11-25T08:01:08.688975+00:00

Dirty AND queries: C5 K7 UNSAT1.720s; C6 K8 UNSAT52.563s. The new query requires all gates useful and some AND gate true on a maximal independent set. Since AND/OR signals are monotone, this is equivalent to a false positive on some input where the graph function is false. It captures higher-cardinality independent assignments, not only singleton/nonedge pairs. The encoder and generated C5/C6 models/outcomes were independently reviewed PASS by lean_setup. These bounded optimum models therefore have all AND signals below the output graph function; no general normalization theorem or Lean result is claimed. C7 K10 dirty query is running separately with native600s cap.

A fixed-prefix obstruction was independently checked in Python and C++ on all64 inputs. Graph edges04,05,12,13 are two disjoint two-edge stars. The pure OR prefix exposes P=0∨1, 2∨4, 2∨3∨4, Q=2∨3∨4∨5, 0∨2, R=0∨2∨3, 1∨4, S=1∨4∨5. Primaries and free constants are also allowed. Three AND gates (P∧Q)∧(R∧S) compute the graph function. Python exhaustively considered repeated-input AND/OR extensions, pruning a prefix once any AND ownership was nonstar, and found no star-profile solution with at most3 new gates (19,867,122 depth3 candidates). C++ independently found no computing extension with at most2 gates; this justifies removing semantic duplicates from a3-gate computation. It then examined2,508,183 depth3 candidates, found18 computing extensions, and found zero with all AND ownership stars. Both programs received reciprocal independent source review.

This blocks a naive three-gate repair with that entire OR prefix fixed. It does not refute L-meta-2448: the original prefix-plus-extension circuit has11 gates, while rebuilding the two star ORs gives an explicit5-gate circuit. The original circuit is therefore not globally minimum. Both complete programs/results and review hashes are preserved, with the dirty query files; manifest now121 artifacts. All evidence remains computational, not Lean-checked.

Updated 2026-11-25T08:12:51.215163+00:00

Both ordered theta attempts also returned UNKNOWN at their native900s limits, with exit0 and no SAT/UNSAT verdict. The independent completeness review of the ordering cut does not turn a timed-out search into a lower-bound result. All8 full model/log artifacts and ordered-theta-outcomes.json are preserved; the source is the already preserved/reviewed synth_sat.py. Manifest now130 artifacts. No further broad theta solver run is planned without a new concrete structural target. C7 dirty query remains in scratch until completion.

Updated 2026-11-25T08:18:26.839507+00:00

C7 dirty-AND query at the canonical10-gate cover size reached the native600s limit with exit0 and no SAT/UNSAT verdict. Outcome UNKNOWN/time-limit; neither a dirty witness nor a cleanliness theorem was obtained. Full model, all logs, exact graph/critical rows, and c7-dirty-outcome.json are preserved. Manifest now137 artifacts. All finite solver work is currently stopped. No targeted essential-star encoder was created: structural_proof found an explicit P4 counterexample to the AND-minimum essential-star hypothesis before that implementation began.

Updated 2026-11-25T08:21:09.931163+00:00
