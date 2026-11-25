# L-meta-2592 orchestration notes

Exact desk data is in /tmp/oec/pequalnp-pilot-102/desk-first.json.
Root holds the only lease for this job. Only root renews and submits.

Strategies: proof_route (structural lower bound), counterexample_route (semantics/search), lean_environment (toolchain), protocol_review (independent checker review).

2026-11-25T14:00:48.509038+00:00 [counterexample_route] Circuit semantics audit found no obvious loophole. Existing reduction slots are all used (318: last-NOT separator; 408: normalization + normalized bound; 271: 15 binary-gate floor + 1..4 NOT bound). Starting CaDiCaL synthesis of 19 gates using existing encoding in notes/data/lrat-link/gennot.py.

2026-11-25T14:01:54.830757+00:00 lower_bound_route: Found checked binary floor in L_meta_4725.lean (3224 lines), adapting branch-count argument credited there to copsrlpond L_meta_2165 and L_meta_1549. Any FanInTwo Petersen circuit has >=15 non-NOT gates, excluding >=5 NOT at total size<=19. Adapted complete source into results/orch/lemmas/BinaryFloor.lean under L_meta_2592 namespace, with final helper binaryFloor; no new full target claimed. Source attribution preserved here. Compilation pending toolchain.

2026-11-25T14:02:44.957422+00:00 [proof_route] Generic last-NOT cut is already checked as L_meta_8295, so discarded my independent untested draft and adapted its 61-line proof into results/orch/lemmas/CutLast.lean under L_meta_2592_aux.CutLast. Source attribution: original L_meta_8295 in upstream. Does not prove hard separator; pivoting to restricted NOT replacement or tight 9-variable cofactor counting.

2026-11-25T14:03:48.423287+00:00 lower_bound_route: Adapted L_meta_5236 source into BinaryFloor16.lean. New realizeTen extracts signed live computation directly from ten pin words, then uses existing atLeastSixteen even when x0 OR x2 is supplied free. Intended result 16+notCount<=size; proof pending compilation. Source attribution: L_meta_5236 reuses L_meta_7306 signed certificate adapted from L_meta_7794 / benoitrazet PR12184, and live-wire/checker certificates L_meta_1667 / L_meta_1677.

2026-11-25T14:04:38.526420+00:00 [counterexample_route] CaDiCaL built in scratch. Boundary-row synthesis produced spurious models: first-NOT 872 wrong rows; first-AND-edge 314 wrong rows. CEGAR now expanded constraints. Full-table local SAT resynthesis around L_meta_587 permits 5 changed gates, one COPY and at least one NOT; first 14 contiguous windows UNSAT in 1–10 seconds each. These are computational observations, not Lean proofs.

2026-11-25T14:07:40.158979+00:00 [proof_route] New ReplaceLast.lean formalizes pointwise last-NOT replacement criteria for arbitrary prefix and monotone suffix: h<=f permits constant true; f<=h permits constant false. Wire-order proof is adapted from existing OneNotPiece.on1_above_snoc/on1_above_wiresFrom; semantic replacement criteria are new in this artifact. Compilation pending toolchain path.

2026-11-25T14:08:16.771112+00:00 [counterexample_route] Finished 40 full-table local 20-to-19 resynthesis windows of five gates in L_meta_587: 31 UNSAT, 9 timeouts, 0 SAT. These are not Lean proofs. Two broad CEGAR searches and one seven-gate local search are paused to give Lean all CPU. Reproducible scripts, solver commit, full logs and summary are under /tmp/oec/pequalnp-pilot-102/counterexample/.

2026-11-25T14:08:59.184245+00:00 [proof_route] ReplaceLast.lean compiled with lake env lean, exit 0, empty compiler diagnostics in /tmp/oec/pequalnp-pilot-102/replace-last-check.log. New replace_true and replace_false criteria independently reviewed by protocol_review. Parent notified to preserve by early push.

2026-11-25T14:09:44.162512+00:00 lower_bound_route: Proposed new binary floor17. For each of360 distinct ordered vertex-pair/signed-op cases, computationally validated two truth-table rows agreeing after pair merge and on other inputs but disagreeing on target. Thus a first binary step retains one input. Ten graph-automorphism projections reduce that retained input to0, making it constant while the first gate itself costs1. Existing projected_bound and nineFloor15 should imply17. Complete Lean extension at BinaryFloor17Extension.lean, pending target16 compilation then testing. Generator/data in scratch lower_bound/.
