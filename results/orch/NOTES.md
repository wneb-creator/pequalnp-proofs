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

2026-11-25T14:14:57.289655+00:00 [proof_route] SensitivityMask.lean compiled cleanly after adding edge_monotone, pair_implicant, negated_mask_implicant. protocol_review independently checked mathematical direction and enumerated all512 assignments (40 sensitive cases,72 distinct ordered pairs). Two-input masks constanttrue on sensitivity domain are constanttrue or NAND of an edge. Thus a last-NOT input whose complement is such a mask is an implicant of the target, so ReplaceLast can replace the NOT by true. Remaining missing structural step: arbitrary small circuits need not present a two-input sensitivity mask. The NOT-on-input ≥4 deletion route remains conjectural: counting dependent gates does not count actual eliminations.

2026-11-25T14:15:59.822064+00:00 [or_case_route] The OR nonedge anti-diagonal projection x2=not x0 has an explicit 15-binary-gate signed circuit: x1 OR x5(x0 OR x8) OR x3(not x0 OR x8) OR x4(x0 OR x9) OR x7(not x0 OR x9) OR x6(x8 OR x9). All512rows checked. Thus this projection cannot raise the17binaryfloor to18 via a16lowerbound.

2026-11-25T14:17:10.866662+00:00 lower_bound_route: BinaryFloor17Extension.lean compiled exit0. All finite pair/projection certificates kernel-checked; Floor17.atLeastSeventeen proved. Standalone BinaryFloor17.lean still needs root integration/build (stronger ten-pin realization and arithmetic wrapper). FirstsignedAND/ANDNOT18 fragment prepared, not yet compiled.

2026-11-25T14:18:57.999506+00:00 lower_bound_route: Verified stronger360 oneDrop collision witnesses (only droppedinput changes); protocol_review independently confirmed. This forcesbothfirstinputs retained. AND/ANDNOT firstgate then yields18binary via2constantmass. Fragment prepared for Lean after17maincompiled. OR leavesduplicate nonconstant; genericduplicatecharge is false (3gateMUX from[a,a,b,c]), so no claimforOR.

2026-11-25T14:19:59.028848+00:00 [or_case_route] AntiDiagonal.lean compiled with lake env lean, exit0 and empty diagnostics. It records an explicit16-gate9-input circuit with1NOT, hence15binary gates, for Petersen restricted by x2=not x0. Independent reviewer exhaustively verified all512rows and legal reads. This blocks one proposed restricted lowerbound, not the posted gap. Parent notified for early push.

2026-11-25T14:21:44.998713+00:00 [root replan ~25 minutes]
- Main checked progress: generic last-NOT replacement; sensitivity mask classification; binaryFloor16; independently reviewed and compiled signed Floor17 extension. Named integrated17 build runs now.
- Active proof route: AND/asymmetric-AND first gate may yield18 binary; OR case remains. No universal duplicate-wire charge (mux counterexample).
- Active search: exact9-input signed15 gate query; then full17binary+2NOT and18binary+1NOT. Local small window resynthesis has no full witness.
- Active lemma route: generalize effective-read compiler, with actual NOT-input exclusion still open. Two literal reads do not alone justify constant replacement (paw-graph obstruction).
- Closed route: OR-nonedge anti-diagonal signed16 lower bound is false; explicit15binary+1NOT restriction circuit is checked and preserved.
- Closed infrastructure route: actual FUSE mount refused with Operation not permitted; fullMathlib checker remains FAULT, no checker edits or fake cache.

UTC 2026-11-25T14:22:32.296547+00:00
### proof_route: effective-read compiler
- Extracted the independent restriction compiler from `L_meta_5367.R` into `results/orch/lemmas/EffectiveReads.lean` (192 lines, 13089 bytes).
- New generalized `lowerReadBound`: if the Petersen-minus-vertex graph has no circuit of size at most k, a circuit supplied x and an extra complement of input zero satisfies k+1+effectiveReads <= size. The count includes actual gate readers of either literal, using only the first operand of a NOT.
- `reads_le_two` specializes to excluded Fin9 size15 and tail size<=18, conditional on that Fin9 bound. This is not a full NOT-input exclusion.
- Compiled with Lean4.36.0, exit0, empty full log `/tmp/oec/pequalnp-pilot-102/effective-reads-check.log`. Independent review requested.
- Exhaustively checked all16 rows of a caution example: d=ab OR e, p=v OR a, q=(NOT v) AND b, output=(p AND q) OR (d AND (p OR q)) equals monotone ab OR ae OR be OR ve, with each literal read once. Neither replacing NOT v by false nor by true preserves the output. Thus the residual two-reader argument needs a real circuit rewrite or stronger target structure.

UTC 2026-11-25T14:26:09.586326+00:00 proof_route sensitivity extension
- New `results/orch/lemmas/SensitivityExtension.lean` (47 lines, 1805 bytes) compiles successfully; full empty log `/tmp/oec/pequalnp-pilot-102/sensitivity-extension-check.log`.
- Every Fin9 assignment outside the edge function and exceptional independent triples135/028 extends upward at one of4/6/7 to a sensitive assignment.
- Consequently any monotone mask vanishing on all sensitive assignments implies edge OR triple135 OR triple028. This is a finite graph-specific bound, not a circuit lower bound.
- Independent protocol review PASS: all512 assignments checked,56 unobstructed cases all extend. EffectiveReads review also PASS and root notified.
- Structural application remains theoretical: for hard two-literal-read form p=v OR A,q=(NOT v) AND B with monotone downstream circuit, at every sensitive assignment the v=0 cofactor of A must be false. Otherwise the v=0 signals dominate the v=1 signals, contradicting output sensitivity. No complete19-gate exclusion follows yet.
