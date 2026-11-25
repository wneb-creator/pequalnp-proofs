# L-meta-2373 orchestration notes

Lease acquired 2026-11-25T12:53:05.140Z. Only root holds and renews lease.
Target: two incomparable subfunctions of the Petersen edge function, computed jointly in 18 gates, cannot cover it. Adding their OR would produce a 19-gate circuit.
Allowed project module: PEqualNP.Defs. Reductions enabled but all three slots occupied.

Agents: status_review (independent mathematics), proof_structure (direct lower bound), counterexample (finite search), library_route (reusable proof source), lean_setup (toolchain/cache).

Each agent may append uniquely named findings. Do not overwrite other sections.

## status_review: mathematical assessment (2026-11-25)

L-meta-2373 is exactly the essential final-OR case of a 19-gate Petersen circuit. If its existential conclusion fails, the two selected wires OR to Petersen on all 1024 rows; incomparability means neither final OR input can be discarded. The three existing reductions are already live: R_meta_2373_1 splits the tail budget 16/17; R_meta_2373_267 normalizes first-gate type and selected wires to Fin18; R_meta_2373_71 uses vertex restrictions (zero bound15, one bound10). The latter zero lower bound is now proved in main by L_meta_670 (directSplit at line6178, final theorem6863), but its source is large and outside imports are forbidden here.

No counterexample or simple contradiction found. The soundness hypotheses alone imply selected wire indices are at least10, incomparability makes them distinct and gives indices below28. A naive fanout counting argument is invalid: in a star-factor circuit a center input can occur once while its three-neighbor OR costs two internal gates. Full proof likely needs the existing restriction/certificate machinery.

## library_route — 2026-11-25T12:56:02.394275+00:00

The target is hOr of R_meta_651_2. Three checked reductions already exist: R_meta_2373_1 splits tail size <=16 versus =17; R_meta_2373_267 normalizes the first gate into distinct-input AND, Fin11-input OR, or Fin11-input NOT and proves both relevant output wires lie in [10,28); R_meta_2373_71 reduces to two 9-input cofactor lower bounds plus a difficult restriction theorem. No fourth reduction slot is free according to desk reductions_live=3.

L_meta_670 (6864 lines, 523341 bytes) proves Petersen-minus-one-vertex has no <=15 gate AND/OR/NOT circuit. This is exactly R_meta_2373_71 hzero. It uses certified live-wire exhaustive search with pruning by separating rows and cofactor lower bounds: BitVec512 truth tables, directSplit at line6178, monoRoot at6852 and signedRoot at6857. Signed mode grants free wire complementation but bounds binary gates by14; mono mode bounds gates by15. Large packed Nat certificates are checked by decide +kernel. New 10-input target requires 1024-bit tables and new certificates. Reusing whole source leaves947 bytes under512KiB before namespace-length changes; comment stripping/dead-code pruning needed.

Existing general EdgeFnPlan lower-bound route only assumes girth>=7 and distinct degree>=3 vertices at distance>=7. Petersen violates both assumptions. LratEncoding root covers AND/OR only, so direct application cannot handle NOT. Current library search found no complete full-Petersen size19 exclusion, only conditional cases (e.g. L_meta_5238 excludes >=5 NOTs after free nonedge OR).

## counterexample — 2026-11-25T12:57:02.861224+00:00

No semantic loophole: the two circuit stages concatenate exactly; out-of-range reads are false. Enumerated all 1024 vertex subsets: minimum vertex cover is6, with5 covers; a star factoring circuit has20 gates. A 19-gate stochastic search currently reaches weighted error6 but no exact witness. Source and complete log: /tmp/oec/pequalnp-pilot-87/counterexample/search.cpp and search-log.txt.

SAT synthesis implementation synth.py uses one-hot AND/OR/NOT selectors, legal earlier-source selectors, free false input (empty AND represented by NOT false), and final OR. Initial91 truth rows are all independent sets plus all weight<=2 assignments. A fixed20-gate reference circuit was SAT-validated on all1024 rows. CaDiCaL search now running for first gate AND(0,1), with all gates live and heuristic sorting of consecutive independent gates. Any SAT witness is checked on all1024 rows; heuristic UNSAT alone is not a theorem. Solver binary is bundled Lean cadical.

## finite_invariants: two disjoint five-cycles

Petersen vertex-cover lower bound6 follows from two disjoint C5s, not an exhaustive search. Any nonnegative integer weights covering each edge have outer-cycle sum≥3 and inner-cycle sum≥3. Both arithmetic lemmas passed Lean4.36.0 (`Core.lean`, exit0) and were inserted as helpers in target file. Python independently enumerated all1024 subsets: minimum cover6, exactly5 minimum covers, 76 total covers. A minimum cover is {1,3,4,5,6,7}. Finset/cardinality bridge being checked. This proves star-cover cost≥20 but alone does not lower-bound arbitrary circuits.

## proof_structure — direct combinatorial route

The standard monotone star formula has20 gates: Petersen has15 edges and vertex cover number6, giving15+6−1. A full unrestricted proof cannot simply assert all inputs have fanout at least2; cover-center inputs may be read once.

The substantial generic route in L_meta_1549 (322455 bytes) proves a 15-gate theta-graph lower bound. Its branching_budget (line6605) gives size≥n+number_of_branch_wires+NOTcount−1 for a least clean circuit. Its class-twin bridge (lines6723–6971) reduces branch count to iterative maximal twin-class deletion in the graph. A Python exact dynamic program over1024 subsets confirms Petersen needs6 such deletions (an optimal sequence is {0},{1},{3},{7},{8},{4,6}). This yields only size≥15+NOTcount, settling≥5 NOTs, consistent with L_meta_5238. It does not settle0–4 NOTs. A stronger weighted fanout invariant would be needed; no such invariant established.

Other genuine lower-bound templates: L_meta_1543 and1547 cover C7 plus3 pendant edges, giving14 gates. These are large gate-elimination developments, not a short reusable full Petersen theorem.

## status_review: independent partial review

Reviewed the initial upper-bound partial and finite_invariants additions before first push. Its15edge terms match the desk statement exactly; independent Python evaluation checked all1024assignments of the20-gate circuit, including all fan-in and earlier-wire index conditions. The two arithmetic lemmas are sound: summing a5-cycle cover inequalities gives2*sum>=5 and hence sum>=3 over Nat; disjoint outer and inner5-cycles give total>=6. Added source uses only omega and prior helper, with no added axioms or forbidden format tokens. This remains PARTIAL: the named target theorem is absent and no checked lower bound is claimed. Reviewed notes and timeline contain no credentials. Lean build is checked separately by root.

Finite helper progress 2026-11-25T12:59:57.427951+00:00: `Finite.lean` passes Lean with no output. It bridges exact Petersen Boolean edge expression to `petersenEdges : Finset (Fin10 × Fin10)`, proves every vertex cover has≥6 vertices, supplies a6-vertex cover, proves every independent set has≤4 vertices, and proves every false input has≤4 true coordinates. A further common-neighbor certificate and biclique-is-star theorem are in progress. Root has the two basic cycle-weight lemmas already.

## lean_setup: kernel certificates — 2026-11-25T13:00:20.215514+00:00

Official Lean v4.36.0 and all 9117 pinned Mathlib cache files are installed under scratch; launcher /tmp/oec/pequalnp-pilot-87/lean-env.sh handles environment. Initial kit warm-cache claim did not match actual environment. No Mathlib theorem sources were built.

Do not use bv_decide: pinned Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean invokes nativeEqTrue at line40 and the tactic adds a compiled-check axiom. Project Library/LRAT/Checker.lean (26553bytes) is an alternative designed for kernel evaluation; checkW_sound F keys width packedWords (by decide +kernel) proves FormulaSat F is false. It stores each clause as a Nat bitmask and each certificate block as at most1024 fixed-width fields inside a Nat under a sentinel top bit. checkFirst/checkSeg/checkLast permit memory-bounded segmented replay.

A general NOT-capable encoding bridge already exists in Library/LRAT/LinkN.lean (55210bytes), with valid_ofCirc covering arbitrary FanInTwo circuits including out-of-range false, and LinkN2.lean supplies the normalized enc2_sat bridge. These are not authorized imports for this gap, so definitions and proofs must be inlined, with Model/Valid/NF structures replaced by existing product types if automatic merge is required. L_meta_5531 (427428bytes) demonstrates an inlined checker using Mathlib BinaryTree and packed proof data. SAT proof size remains the likely obstacle.

L_meta_670 already packs its finite-search data: removing line comments and blank lines only shrinks523341to522639bytes. Indentation totals another14049bytes, so trivial text compression will not buy much. PR12203 has empty body and only the one proof file, with no generator link; it timed out repeatedly and closed after another proof merged. No generator found in current tools/Library filename scan.

2026-11-25T13:02:49.279368+00:00: `Biclique.lean` and `BicliqueFast.lean` both Lean-checked. The former is preserved as results/orch/lemmas/FiniteInvariants.lean. New facts: every distinct pair has at most one common neighbor; hence every complete bipartite subgraph of Petersen has one side of cardinality≤1. This is the biclique-is-star step needed for a monotone lower bound. Generic biclique-cover number≥6 proof is being checked next.

## status_review: second partial review

Reviewed changes after501d6e75 adding petersenEdges, vertex_cover_size, minimum_vertex_cover, independent_set_size, edge_eq_false_iff, and false_input_support_size. The Finset contains exactly the posted15edges. Cover bound6 follows the two disjoint odd5-cycles; explicit witness {1,3,4,5,6,7} covers every edge. Complement reasoning correctly bounds independent sets by4, and the Boolean bridge gives false-input support size<=4. No forbidden source tokens or new axioms; no change to theorem objective. PASS as additional PARTIAL results, subject to root Lean build.

2026-11-25T13:05:33.211980+00:00: Generic `biclique_cover_size` also Lean-checked (scratch BicliqueCover.lean, exit0); preserved with all finite invariants in results/orch/lemmas/FiniteInvariants.lean. Any family of k complete bipartite subgraphs covering Petersen edges has k≥6: each biclique is a star, choose one center per family member, obtain a vertex cover of size≤k, apply mincover6. No circuit correspondence is assumed: intermediate AND outputs can contain extraneous pairs later removed by AND, so a separate normal-form argument is required.

## proof_structure — checked binary-count partial

Adapted the generic petersen_binary_lower development from L_meta_5238 (itself based on L_meta_2165/L_meta_1549), not merely its specialized final theorem. Standalone source results/orch/lemmas/BinaryLower.lean proves for every FanInTwo circuit computing the exact Petersen function: 15 + NotBracket.notCount C ≤ C.size. Consequently no circuit of size≤19 with≥5NOT gates computes it. This remains a PARTIAL: cases0–4NOT are open.

Lean compilation completed with exit0; complete linter-only output is preserved in BinaryLower.compile.txt. The three custom datatypes were replaced with Sum Bool Nat, a product, and a conjunction predicate; all helper simp attributes are local. Independent review by lean_setup passed for source SHA2568f3f7098e38a6e84ee3f96515594eb165adfb88532e63dc26d7856cd72e19931.

## status_review: backup artifact review

Independent review: status_review
FiniteInvariants.lean: PASS as a partial helper artifact. Checked cover>=6, independence<=4, false-input support<=4, common-neighbor<=1, bicliques are stars, and any biclique cover needs>=6 blocks. Helpers do not prove the target circuit lower bound. Plain-file restrictions pass; build checked separately.
Search backup: PASS for preservation. Read all four programs and manifests/logs. No network or credential access in code; no credentials found in artifact text. Every stored manifest hash/bytecount matches. All programs concern the exact15edge Petersen function. Full1024row witness validation is present; search heuristics/UNSAT/UNKNOWN are explicitly not presented as a lower-bound proof. Initial stochastic weighted mismatch6 means six false negatives and no false positives.
Automorphisms.lean and its full empty success log were preserved by its author for a separate independent review.

## lean_setup: Live1024 verifier/extraction — 2026-11-25T13:08:10.636846+00:00

Compiled exit0: results/orch/lemmas/Live1024.lean,1251lines61643bytes,SHA256 ff6605ddff5663cec2f175069edab7ad015c18e1f641da70d82b6151ec116e1b. Complete compiler output in Live1024.compile.txt. Uses only PEqualNP.Defs. No newdatatypes,instances,axioms,sorry,native_decide,bv_decide,strings,or rootnamespace escape.

Adaptation from checked L_meta_670: retain generic source lines1–746 and768–1171 (width512→1024), regenerate teninputsignatures and fullPetersen truthtable(948positive,76negative rows), adapt table_eval and twoRoots/directSplit to10inputs and19totalgates. Exact Live semantics match library_route: fresh proper output from two distinct live operands, optionalretention of either operand, signed opsAND/OR/ANDNOT/NOTAND, freecomplement normalization atrow0. Included Reach,Run,projected_bound,list_run,Lower,Impossible,enum_step,Sep/cover_required,Slice/poolCut_sound.

Top conditional theorem directSplit: excluding monoLive≤19 and signedLive≤18 excludes≤19gate circuits. This is only a ready-to-fill certificate framework, not a checked lowerbound; neither exclusion is claimed. A signed18binary witness alone would not refute the original19totalgate claim unless its NOT cost is≤1. No Forest packing or cofactorlowerbounds are included yet.

## status_review: conditional bridge review

Independent Bridge.lean review by status_review: PASS as partial conditional bridge.
The glued circuit evaluates the first gate, the original tail, then OR(u,v), with outputindex11+C.size equal to the final appended wire. FanInTwo is inherited and size=C.size+2<=19. Exact graph expression matches postedPetersen. cover_gives_circuit has the correct orientation of Boolean equality. missed_of_no_circuit uses soundness plus failure of existential to produce exact coverage, contradicting its explicit lower-bound hypothesis. It does not prove that lower-bound hypothesis and does not claim the target theorem. No forbidden source tokens/newaxioms. Full compilelog preserves the queuewaitmessage; root reports compilerexit0.

Counterexample update at2026-11-25T13:08Z: initial stochastic run completed2,120,500,000 evaluations (8,482 restarts), best weighted error6: exactly six false negatives and zero false positives. Global SAT firstAND-edge and firstNOT-input each timed out UNKNOWN at600 seconds. From-scratch20-gate monotone positive control likewise timed out120 seconds, showing general synthesis is too hard for this encoding. Fixed20 controls are SAT. Source and complete finished logs+SHA256 manifest are now in results/orch/search/. Local incrementalSAT is still running; no full19-gate witness.

## status_review: cofactor search certificates

Implemented search-side cofactor pruning in scratch cofactor_prune.py, coordinated with library_route. The exact-Live projected_bound counts every live root made constant (unlike Lower_slice on an arbitrary available pool, which requires essentiality). A paid replay of the projected prefix supplies the remaining live roots; aliases, constant outputs, and dead replay gates are removed. Cuts use lower+constant_mass>remaining+paid. Transported L_meta_670 bounds give16(monotone)/15(free-signed) for every vertex-zero cofactor and11 in bothmodes for vertex-one (three essential neighbor literals plus a six-cycle lower8). Extracting known383/known511 and their checked transports gives tight star-cover bounds for all<=8vertex inducedPetersen subgraphs; the ten9vertex signed bounds are onebelow star-cover upper16.

The65restriction version includes10single-zero,10single-one,45double-zero cofactors. It passes no-false-prune checks on all21states of the explicit20gate circuit in bothmodes. Constructive paid replays additionally passed2000random checks. Directonegate synthesis seeds did not eliminate any of the first1000depth7survivors (2.69seconds), so that optimization has no demonstrated benefit. These Python bounds/cuts are search aids; new target Lean certificates still required.

Live1024 count-extension 2026-11-25T13:11:57.314814+00:00: results/orch/lemmas/Live1024Count.lean compiled exit0, SHA256 686e0602a87a99ee2fed49ec3809d8e99cff0227d6b5664eb6e42b7f620302f0. Adds only circuit_live and circuit_live_signed to prior checkedframework; exposes exact countP(nonNOT) budget without19gateassumption. Full compilelog preserved. Original reviewedLive1024copy left unchanged. This enables proof_structure to combine projected_bound with ninevertexsignedlower15 and derive fullPetersenbinarylower16.

2026-11-25T13:12:54.338177+00:00: NoOrIdentification.lean compiledexit0. For every distinctvertexpaira,b, finite kernelchecked separatorc≠a,b makes edge({a,c}) true and edge({b,c}) false. These assignments agreeoutsidea,b and have equalOR ofa,b. Preserved results/orch/lemmas/NoOrIdentification.lean and completeemptycompilerlog. Target135-line build with finitecoverhelpers also finishedexit0.

## Root replan, 2026-11-25T13:13:07.310543+00:00

The first twenty minutes produced checked partials but no target theorem. Global SAT is too slow even on the unseeded twenty-gate positive control; stop expanding that route and finish existing local/relaxed searches. The basic branch-count route is complete at fifteen binary gates. Prioritize the signed nine-variable certificate and restriction bridge toward sixteen or seventeen binary gates, which would reduce the remaining NOT cases. In parallel prioritize Live search with the newly strengthened cofactor cuts and read-once terminal closure; every pruning rule must have a Lean proof before any exhaustion result is claimed. Finite graph facts are sufficient; only the no-OR-identification lemma and necessary symmetry transport merit further work. Continue five-minute lease beats and preserve checked components after independent review.

## status_review: OR-identification review

Independent NoOrIdentification.lean review by status_review: PASS as helper partial.
Checked exactPetersen expression and all90ordered distinctvertexpairs independently: each has a thirdvertex c adjacent to a and notadjacent to b. pairInput(a,c) and pairInput(b,c) agree outside a,b and have equal OR at a,b, but different graphoutputs. This proves loss of information when identifying any two variables by OR. Kerneldecide handles a finite10^3certificate, and subsequent proof uses onlythose conclusions. No newaxioms or forbidden plain-file tokens/options/attributes. Compilelog preserved(empty); root reports success. This is not the target circuitlowerbound.

### library_route search update 2026-11-25T13:17:54.484636+00:00

Implemented exact Live-state computational search in scratch library_route/live_search.py and several C++variants. Full1024-bit wire truth tables; actual fanout handled by retaining/deleting operands. Monotone samples are15edge rows×15maximal independent sets; signed mode uses15edge rows×76independent sets. States canonicalized by Petersen graph automorphisms stabilizing firstgate. No full exhaustion or counterexample yet.

Cofactor cuts provided by status_review:10single0,10single1,45double0 then240mixed/triple0 profiles. The extra240rejected982/1000surviving depth7states. Another840profiles left6survivors, and exhaustive17522proper nonconstant restrictions killednoneofthose6. All6have sharingdeficit1.

Terminal oracle atdeficit0 computes sparse closure of pairs(maskoforiginalleaves, truthfunction). Combine disjointmask entries; keep onlyoutputs covering row-separation obligations notalready covered by outside originalleaves. For one13leafstate there were63closureentries and nofulltarget;25sample states allrejected in~0.2sPython. Atdeficit1, enumerate sharedsubexpression (a readonce subformula onleafsubsetA), replaceA bytwo copiesofthatwire, theninvoke deficit0closure. All6strongcofactor survivors rejected in0.7s; eachhad15–17possible sharedsubexpressions. Lean_setup is formalizingδ0closure, parent arrangingδ1decomposition.

Current C++live_search_allcuts.cpp uses1145profiles plus deficit0/1oracles; running bounded180s firstANDedge. Experimental lexordering variants exist but are notused inlatest search and noresult is basedonthem (earlier logs withbothlexorder andnontrivialsymmetry are notsound asquotientsearch). All longdiagnostics savedcomplete in scratch.

## status_review: tight Live induction review

Independent Live1024Tight review by status_review: PASS for the added tight_induction helper.
Compared against Live1024Count.lean: only the32-line helper and whitespace were added. With S.card=k+1, live_size on the tail forces both operands absent from U, hence every step consumes both input wires and the tail again has cardinality k+1. Freshness justifies the tail-cardinality rewrite; cardinal bounds plus omega establish the two nonmembership facts without additional assumptions. The induction returns P S from the stated stop and step premises. No new axioms, definitions, options, attributes, imports, or forbidden tokens. Full compile log contains only existing linter/deprecation warnings; root reports success. This helper characterizes tight Live runs and does not itself prove the target lower bound.

2026-11-25T13:19:20.471455+00:00: ExactLive1024 table-level ORidentificationwitness compiledexit0. Artifact results/orch/lemmas/NoOrRows.lean, completecompilelogretained. For eachdistincta,b, it searches onlyc:Fin10 andreturns pairRow(a,c),pairRow(b,c) that agreeonallotherinputcolumns, agreeonbin1(OR), butdifferentgraphbits. TabledefinitionscopiedexactlyfromreviewedLive1024. AllmyLeanrunsnowfinished; pausednewrunsforrootsolochecker. UpperFast3norm_num+AC attemptfailedsameinnerANDorientationissue; no sourcechange made totarget.

## status_review: row-level OR identification review

Independent NoOrRows review by status_review: PASS as partial row-level helper.
All ten input tables and the target graph table exactly match Live1024Count. Independently verified all90 ordered distinct input pairs have a c whose two pair rows agree on every other input and on the OR word, but disagree on graph. pairRow stays within0..1023. The final existential theorem directly packages the finite kernel certificate. No forbidden source tokens or new axioms; full compilation log preserves queue waits only, and author reports exit0. This helper excludes identifying both OR operands and does not claim the target lower bound.

## status_review: checked symmetry projection

RowProjection.lean compiled with exit0; the complete log contains only a queue wait. It defines rowMap(v,r) by permuting the nine row bits through relabel(v), setting original vertexv tofalse. Three kernel-checked table identities prove: the10-variable graph restricted along rowMap equals the9-variable graph; inputv is constantlyfalse; and input relabel(v,j.castSucc) becomes nine-variable inputj. Source and full log preserved under results/orch/lemmas, with an appendable suffix for proof_structure. Observed RSS during compilation was about6.7GiB, so large proof checks must run alone.

## counterexample final search outcome — 2026-11-25T13:22:41.104503+00:00

All bounded searches completed without a target witness. Four stochastic runs used8,325,500,000 heuristic evaluations total: ordinary19 best6 false negatives; hotter ordinary19 best9; signed19 best9; signed18 best15. Both best signed candidates normalize to monotone circuits, so neither challenges the signed18 exclusion framework. Global19 SAT cases (firstAND-edge, firstNOT-input, firstOR-nonedge, and a root-last/at-most-one-NOT case) each returned UNKNOWN after600 seconds. Unseeded20 monotone controls likewise returned UNKNOWN after120 seconds; fixed20 controls passed. LocalSAT:286 all-row neighborhoods gave1UNSAT/285UNKNOWN;1118 promise neighborhoods gave27UNSAT/1091UNKNOWN. No search result is presented as a general lower bound. Final source, full logs, README and SHA256/size manifest are preserved under results/orch/search/.

Counterexample archive correction: independent review verified6false negatives and0false positives for the best ordinary19 candidate, but it is not equal to the graph function after deleting any one edge. Earlier stronger wording was an incorrect inference from its missed assignments and has been corrected. No mathematical proof or search verdict is affected.

## status_review: projection availability and subtree profile

2026-11-25T13:31:47.411527+00:00

RowAvailability.lean compiled with exit 0. Its conditional lemma rowMap_available_of combines the already checked rowMap_missing and rowMap_input identities with relabel bijectivity, supplying every projected primary input from the signed nine-input pool. Full source, reusable suffix, and complete compiler output are preserved under results/orch/lemmas. Independent review requested from finite_invariants.

Exploratory subtree pruning: on library_route's 18-root closure cap snapshot, checking each read-once candidate subtree as a reordered prefix reduced the closure from a 3,003-entry cap to a complete 36-entry closure without the target. It rejected 240 of 266 candidates in 0.079 seconds. This is not a Lean result: the first-sharing/reordering decomposition still needs proof. Source and full output remain in status_review scratch for library_route integration.

### lean_setup δ0 sparse closure verifier, 2026-11-25T13:32:19.742872+00:00

Checked `results/orch/lemmas/Live1024Closure.lean`: 1524 lines, 74720 bytes, SHA256 `d5325b37a5b30122a2d9bc40d1f741174e287e22d8d7f58095a3deef0655b499`. Full Lean compile exit0; 16 preexisting linter warnings, no errors. Adds finite root-partition, column support/admissibility invariants, tight Live closure-state induction, raw root initialization, impossible-target corollary, and both monotone/signed row-separation columns. Cert remains an abstract predicate: this proves a certificate verifier interface, not an exhaustive Petersen certificate or the posted theorem. Complete output beside source. Fresh-input/nonalias-output variant prepared separately to shrink duplicated-root tables; not yet compiled.

### lean_setup fresh δ0 closure, 2026-11-25T13:33:17.296888+00:00

Checked `results/orch/lemmas/Live1024ClosureFresh.lean`: 1609 lines, 79318 bytes, SHA256 `b48532d73a1eb0529a4b454118bbb0b83e4953dfb59612a51a0f0b66b69817ef`. Full Lean compile exit0, 16 linter warnings. `tight_closure_fresh_state/raw/exclusion` allow closure tables to omit equal operands and outputs equal to either operand, since actual Live transitions forbid these cases. Original closure interfaces preserved by a wrapper. Saved scratch module object `live1024/Live1024ClosureFresh.olean` for later wrapper debugging. Still a conditional verifier only.

2026-11-25T13:36:24.300872+00:00: ConditionalInfluence.lean passes a frozen Defs-only recheck with exit0 and empty output. For any distinct a,b and any fixed value of b, there are inputs differing only at a with different edge values. Therefore every bin0..3 loses essential information if either first-gate operand is removed. ConditionalRowsDraft bridges the explicit finite supports to Live1024 row witnesses next; no arbitrary-function or Fin1024-pair enumeration.

2026-11-25T13:37:48.736827+00:00: ConditionalRows.lean passes Lean with Defs-only import, exit0 and empty output. It bridges explicit one-/two-/three-input supports to Live1024 rows by small Fin10-index identities, then proves no_binary_identification_left_rows for every d<4. The rows agree on every input except a, agree on the new gate, and disagree on the target. The symmetric right-operand fact follows by swapping inputs and flipping op2/op3. This can force both first-gate operands retained and supports an18-binary lower bound in first-AND cases. No full20-gate lower bound is claimed.

## counterexample agent: checkedδ1 terminal oracle — 2026-11-25T13:38:51.261895+00:00

Live1024DeltaOne.lean compiled with exit0; sourceSHA2566032bb5579426da3fd9f6b50cf04d57b0665fd659212268fbedc17821d1bee46,2172lines108068bytes. Full compiler output preserved inLive1024DeltaOne.compile.txt. New562-line fragmentDeltaOneLemma.txt proves first-retention decomposition preservingread-once Cert0 labels/columns, duplicated Sum α Bool rootpartition/support, finite Cert0→Cert2 bridge, and deficit_one_closure_exclusion (Impossible forbudget≤numberofroots). Thetightcase usesδ0; oneextra-gatecase necessarily hasonesingle-retentiontransition andthena tighttail. Noformula reordering or Runcommutation is assumed. CopyCertificate obligations remainexplicitfiniteclosure/transfer/missing-target checks; targetPetersen lowerbound isnot yetproved. Independentmath/trust/format reviewPASS bylean_setup; library_route regressionchecked950nonvacuousbridge obligations across6archivedfrontiers inPython. Rootauthorizedarchiveforimmediatepartialpush.

## proof_structure signed cofactor checkpoint (2026-11-25T13:42:24.137889+00:00)

Checked artifact `results/orch/lemmas/NineSignedReach.lean` proves `NineSigned.nine_binary_lower` and `NineSigned.nine_reach_lower`: the vertex9-deleted Petersen function requires15 binary gates even with free complements. The signed-only L670 certificate is retained unchanged except namespace, with two new wrappers;246–247KB total. Compiler exit0 with warnings only; full log preserved. Scratch cached module `NineSignedCore.olean` enables lightweight extension tests. This is a partial result, not the posted2373 theorem.

2026-11-25T13:42:56.425528+00:00: FirstOperandsRetained.lean compiled exit0. New first_binary_operands_retained proves both original input columns must remain inU after the first Live step for any allowed signed operation. It uses the strong per-operand row witnesses and live_row_difference, then bin_flip for the second operand. The pool equality justifies U⊆original inputs. Complete source, standalone suffix, and full compiler log preserved under results/orch/lemmas; only preexisting linter warnings.

### lean_setup finite and witness reflection adapters, 2026-11-25T13:47:43.920466+00:00

Compiled `results/orch/lemmas/Live1024WitnessTables.lean`, 87770 bytes/1761 lines, SHA `95ed9bee401c2672d58bb092947853f326700c9e322c85163a1502052647eba4`, exit0 with 16 inherited linter warnings. Contains generic finite-column table closure/bridge checks plus faster single-rejecting-row witness checks. Both use bounded Finset/table/range4 quantifiers and kernel-only decidability. The witness check validates a candidate table entry or one required row pair missed by the candidate and every outside root. This directly contradicts column admissibility and avoids constructing225-element column sets. Counterexample independently reviewed both adapters; its concrete12-root terminal certificate build is underway.

### Counterexample / concrete δ1 certificate (2026-11-25 13:48:14 UTC)

State0 initial13-entry fresh closure now kernel-checked with row-witness reflection. Full standalone source `lemmas/Live1024Terminal0Closure.lean`, SHA2567b8ccd2b8e5c38716ec6f972a942fb7b7788f114fa58b716c0bdc3b5fff4f331; Lean exit0, complete log archived. All85 signal literals,225 pair rows,13copytables and their untrusted packed row-witness data are declared; only oldTable closure is proved in this intermediate artifact. Full13copyclosure/bridge checks and `terminal_excluded` currently compiling. Plain225-element Finset union checker exceeded10.9GB RSS and was safely terminated; witness adapter avoids materializing columns and checks only chosen blocking rows. No target theorem claimed.


### library_route: closure certificates and optimized search (2026-11-25T13:48:56.483244+00:00)

- Full signed row separation uses all positive rows via bitset intersections against each of the76 false rows. It independently confirms both operands must survive every first binary gate.
- Fresh δ0/δ1 tables omit operand-alias outputs, justified by actual Live freshness against insert a (insert b U). Six concrete deep-state datasets were exported, with83–99 shared signals and312–397 copied-closure entries each. Independent audit checked37,466 candidate operations and950 finite bridge obligations. These are partial-state exclusions, not the full target.
- General first-sharing recurrence remains experimental. Subtree cofactor pruning reduced a capped3003-entry closure to36 entries. Its missing generic reordering argument must use list Run because moved subtrees may coincide with outside root values.
- Ordinary Live search now uses full signed dependency checks, fresh closure terminals, a compact restricted-value dictionary, lazy cofactor caches, and input-prefix filtering of graph symmetries. The full120 Petersen automorphisms are valid for state impossibility even inside a fixed first-gate experiment; independent review confirmed no historical transition filter remains.
- Positive control: an independently generated20-gate star-cover witness passed all21 exact-live states in both modes, including10 δ0/δ1 terminal checks per mode. No full19-gate exclusion or counterexample has been obtained.

## Root second replan, 2026-11-25T13:49:30.406328+00:00

The trimmed98-line target builds with PEqualNP.Defs only and the repository checker now completes: REJECTED (no-theorem), accurately identifying the unfinished goal. The checked20-gate control remains preserved in TargetPartial135.lean and history. Research builds can use two narrow-import slots; full checker runs get a quiet window.

Prioritize concrete Petersen seventeen-binary-gate instantiation using the now-cached checked nine-input certificate. Finish its nineteen-gate/NOT-count consequence before expanding more variants. The generic delta-zero/delta-one terminal checker is checked; produce concrete frontier exclusions next. Favor conventional Live search with full functional-dependence, cofactor cuts, and these terminal rules; keep unproved first-sharing recurrence experiments secondary. All heuristic searches remain incomplete, and no exact counterexample has been found.

### Counterexample / checked concrete terminal0 (2026-11-25 13:57:01 UTC)

`lemmas/Live1024Terminal0.lean` now proves `Terminal0.terminal_excluded : Impossible false graph 12 (roots.image raw)` for the exported12-wire frontier. This is an actual terminal exclusion, using all13 checked copied bases (318 Cert2 entries), the old13-entry table, every bridge, correct graph signature, distinct raw inputs, and valid225 separation pairs. All checks are kernel `decide`; no native evaluation or unproved hypotheses. Declaration-local resource limits satisfy repository format. Final source245134bytes, SHA25644d4eeedc4fa48cd1f7d8b3048f3d4ddd4be435e6e0de44aa24e1e4633ce7b4a; localized standalone build EXIT0, complete log archived. General gap L-meta-2373 remains unproved. Independent exact-source review is `review-terminal0-complete.txt`; initial global-limit artifact remains historical only.

### Counterexample / arbitrary positive deficit decomposition (2026-11-25 13:59:23 UTC)

`positive_deficit_first_retention` is now Lean-checked. From any actual Live run with positive deficit δ = k+1−|S| and a closure/partition/support invariant, it finds the first retained operand after a no-retention prefix. A single-retention transition leaves deficit δ−1; a double-retention transition forces δ≥2 and leaves deficit δ−2. Actual tail run and every invariant are preserved. This is the cardinal/state decomposition, not yet full hierarchy soundness. Source `lemmas/Live1024FirstRetention.lean`, SHA256a2122aef06514264db749fbcd43187a07e942da0c6977bee78c4a7ba707866de; full compile output archived, EXIT0. New76-line fragment independently mathematically reviewed by lean_setup.

## proof_structure concrete17 checkpoint (2026-11-25T13:59:40.738997+00:00)

`results/orch/lemmas/PetersenSeventeenFull.lean` is self-contained, sole import `PEqualNP.Defs`,330182bytes7156lines, and compiled exit0. It preserves the previous target facts and proves `petersen_not_budget_seventeen`:17+NOTcount≤size for any legal circuit computing the exact Petersen edge function. Thus `petersen_three_not_exclusion` excludes size≤19 with at least3NOT gates. This remains a partial; the posted2373 theorem is intentionally absent. Independent review: `review-petersen-seventeen-full.txt`. All compiler output saved beside source.

## proof_structure eighteen-first-step checkpoint (2026-11-25T14:00:29.038396+00:00)

Checked `PetersenEighteenExtension.lean` imports the checked standalone17 module and adds: two distinct constant frontier entries cost2 after projection; every normalized first binary gate retains both original operands; every first gate other than OR requires at least18 binary gates. `signed_seventeen_or_roots` reduces any17-binary signed Petersen run to a16-gate continuation from all10 inputs plus one OR of two distinct inputs. `two_not_or_roots` gives the same conclusion from a size≤19 circuit with at least2NOT gates. This does not rule out the first-OR case or prove full20. Append-only source is `EighteenFullExtension.txt`, with full compiler output beside the tested module.

### finite_invariants: double-sharing partition and support, 2026-11-25

Checked `results/orch/lemmas/DoubleSharing.lean` (exit0; full log beside source). The suffix implements `doubleSharingLabels`, `double_sharing_partition`, and `double_sharing_support` for a first binary transition retaining both operands. The nested duplicate basis has two copies of each operand; one copy remains at each old operand and one copy of each labels the fresh output. Unaffected labels are lifted twice. No reordering or injectivity after projection is assumed. Source fragment: `DoubleSharingSuffix.txt`; intended for counterexample agent hierarchy induction.

### Counterexample / hierarchy interface (2026-11-25 14:03:10 UTC)

Checked `sharing_cert_state` preserves arbitrary-tail partition, certificate entries, and support after one retained operand, without δ0 tightness. Checked `CertificateTower` recursively requires fresh closure, missing full target, and single-copy successor certificates with finite bridges. This defines conditional hierarchy data; general soundness is still being proved. Source `lemmas/Live1024HierarchyDraft.lean`, SHA256bff332a4ffe4c0d095aaf6cd26e5226ab54c7e512f4accc415225e2f1682057b; EXIT0. Independent finite_invariants review PASS at `review-hierarchy-draft.txt`.

### lean_setup generic Run composition, 2026-11-25T14:03:58.304677+00:00

Compiled `results/orch/lemmas/Live1024RunCompose.lean`, SHA `4d5016fe2ea5cfd2bcddb347c53fc5cc9e981aca93d60179ba50736d8f7b1921`, 65362bytes/1331lines; exit0 with16linterwarnings. New36line fragment proves `Run.substitute`: compose a Run producing one wire with a continuation using that wire, retaining an arbitrary extra root list. `Run.combine_traces` composes two independently computed operands then one binary operation with exact additive gate count. Both are generic in row type and signed/monotone mode. This supports replacing most copied finite tables with ReadOnce predicates plus cofactor cuts.

### finite_invariants: memo automorphism transport, 2026-11-25

Checked `MemoRename.lean` (exit0, full log archived). Five thin lemmas transfer exact or bounded impossibility through the existing checked `live_rename`: row map is surjective, target is fixed, and current pool image equals the earlier pool. Explicit right-inverse variants support finite witness checking. This is only a conditional memo rule; no particular permutation or whole search certificate is asserted. The reusable fragment is `MemoRenameSuffix.txt`.

### lean_setup ReadOnce support calculus, 2026-11-25T14:05:36.343673+00:00

Compiled `results/orch/lemmas/Live1024ReadOnce.lean`: 68633bytes/1400lines, SHA `0203de82d93aed8b85fadc1d1b5d0c3b2f09b0a782b3bc5a09bae460d6690887`, exit0/16linterwarnings. ReadOnce(raw,u,A,v) means nonempty supportA and a Run computingv from its raw leaves with exactly|A|−1gates. The new68lines prove singleton leaves, binary closure under disjoint supports, and injective relabeling preserving raw signatures. Taking Cert0=tableCert∧ReadOnce establishes actual-prefix provenance automatically; taking Cert2=ReadOnce on duplicated roots gives the copied-basis bridge via Sum.inl. Cofactor cuts can then prove absence of full-target ReadOnce, replacing most large copied tables. Exact lower-bound source mapping for exported cuts is being checked with library_route.

### Counterexample / general certificate hierarchy soundness (2026-11-25 14:07:26 UTC)

`certificate_tower_exclusion_state` and raw-basis wrapper `certificate_tower_exclusion` now compile. A depth-d certificate tower excludes any actual Live run with k+1≤|S|+d under the label partition/certificate/support invariant. Zero deficit uses δ0 closure; positive deficit passes to the checked first-retention decomposition. One retained operand consumes one copied-basis successor; two retained operands consume two sequential successors. The double case uses fresh basis row cover to certify the consumed a-copy, avoiding any Run-reordering assumption. All transitions preserve the actual tail and its invariants. Final source `lemmas/Live1024CertificateTower.lean`, SHA256261401f9c324ac1991a2285df47063f2746cc18f5771f7012580712632098b66, 139048bytes; EXIT0 with full log archived. This is a conditional general certificate checker, not a complete certificate for the original gap. Arbitrary-depth cofactor terminal cuts still need a separate ReadOnce forest/Run composition bridge; depth0 closure leaves and existing δ1 finite tables are covered.

### finite_invariants: positive Petersen cofactors, 2026-11-25

Checked `PositiveCofactors.lean` against the cached `PetersenSeventeenFull` module (exit0; empty full log archived). `positiveNine` is nine-variable graph OR x4 OR x6 OR x7, exactly full Petersen with vertex9 fixed1; its signed binary lower bound is11. `positiveAdjacentZero` is graphGoal495 OR x6 OR x7 on vars495, additionally fixing vertex4=0; its lower bound is10. Both clear4,6,7 with explicit row moves and lift graphGoal303 C6 lower8 from `valid189`, adding three or two checked essential literals. Generic `lower_mode_of_signed` exposes monotone consequences. Reusable fragment `PositiveCofactorsSuffix.txt` must be included after NineSigned core in a standalone file; the small cache-import artifact itself is for research.

## Root re-plan at approximately 80 minutes

The concrete signed binary lower bound is 17, excluding size-19 circuits with at least three NOT gates. The checked extension excludes first non-OR gates at binary budget17 and reduces the two-NOT case to a first OR; the zero/one-NOT cases remain open. The current named-file lake build passed. No exact gap theorem has been supplied.

The full Live search has completed useful subtrees but not either whole first-OR case. Continue the reproducible signed17 OR-edge case with hash-bound completed-state resumption. Do not extrapolate a runtime or claim the stronger signed20 lower bound.

The arbitrary-depth certificate-tower theorem now supplies a sound sharing recurrence. Prioritize concrete certificates: close the exported successor node with existing cofactor lower bounds, and replace expensive copied-basis tables by checked ReadOnce/cofactor cuts. The forest-Run bridge is needed before treating the old cofactor-pruned copy search as certified. Each new abstract helper should serve one of these concrete obligations.

The small-row SAT route returned UNKNOWN for both the known20 monotone control and the19-gate one-NOT search. Stop allocating more solver runs to that encoding. Preserve full logs and its limits. Every compiled, independently reviewed milestone is pushed promptly; no PR is opened for partial helpers.

### finite_invariants: positive profile transport, 2026-11-25

`PositiveProfiles.lean` compiled exit0 with all finite kernel checks. Its four cases represent profile IDs14,76,101,123. Each explicit Fin10 permutation maps canonical vertex9 to the positive vertex, and for the last three maps vertex4 to the zero vertex. `rows` embeds 512 canonical assignments into the correct1024-row cofactor. Domain membership, target equality, all ten input images, and available-root membership are verified; the target lower11/10 lemmas apply in either mode. This supplies all positive transports needed by the306-child fixture. A generic Slice bridge and thin constructors are being integrated separately.

### Counterexample / checked ReadOnce forest bridge (2026-11-25 14:15:21 UTC)

`readOnce_forest_run` now proves: actual Live target run of k gates from live set S, plus a root-label partition and ReadOnce derivation for every live wire, gives an actual Run from the full raw-root list with exactly k+|roots|−|S| gates. `readOnce_forest_exclusion_state` consumes any bounded-Run contradiction at depth d and rules out the actual live state whenever k+1≤|S|+d. The list substitution preserves duplicate raw signatures; partition labels remain distinct. This is the missing bridge for arbitrary-depth copied-root cofactor leaves. It does not itself construct the cofactor proof or validate closure-entry pruning, whose partial-substitution variant remains to be integrated. Source `lemmas/Live1024ReadOnceForest.lean`, SHA2564abb09b3d0ac362a96d2e325001e383b2c9c87e9bf4812c855134ad4d16c30a1; EXIT0, full log archived. status_review mathematically reviewed the substitution/forest fragments and is finalizing the immutable source audit.

### 2026-11-25T14:18:30.685375+00:00 lean_setup
Checked SliceFromNine (96 lines, 4173 bytes) transports arbitrary nine-variable Lower bounds to Live1024.Slice using a coarse/section retraction; no finite data or new assumptions. Source and full EXIT0 log archived in lemmas/. Independent reviews by finite_invariants and proof_structure. All 14 zero/positive cofactor profile transports are prepared by finite_invariants.
Compact cofactor plan: poolCut_run_sound removes only the Live-to-Run conversion from existing poolCut_sound, retaining duplicate basis wires. Draft state4/candidate14 proves a cap11 Run exclusion from vertex8=0, lower15, one constant, and four paid gates. This is a positive-depth tower consumer; awaiting root checker resource window before builds.

### finite_invariants: all fourteen concrete Slice profiles, 2026-11-25

`SliceProfiles.lean` compiled successfully and generated its cache. The aggregate `PEqualNP.Outside.L_meta_2373.SliceProfiles.all_slices` supplies the profile ordering [0,1,2,3,4,5,6,7,8,9,14,76,101,123] in either signed or monotone mode. Its `domains` and `bounds` lists match every known cofactor child in fixture126663. Reusable constructors are in `SliceProfileConstructors.txt`; the small module also contains the previously checked generic Slice bridge and positive/zero transport suffixes. Cache path: `/tmp/oec/pequalnp-pilot-87/finite_invariants/SliceProfiles.olean`. This is concrete cofactor certification, not full Petersen search exhaustion.

2026-11-25T14:23:55.896306+00:00 lean_setup: State4Copy14 compiled EXIT0, source6713 bytes, no Lean warnings/errors. The generic duplicate-preserving Run pool cut also compiled, with independent review PASS. Exact signed/mono cap11 exclusion now available; counterexample is instantiating the concrete positive-depth forest theorem. All14 SliceProfiles compiled and independently reviewed.

### Counterexample / concrete positive-depth cofactor consumer (2026-11-25 14:25:06 UTC)

`State4Copy14.forest_excluded` now compiles for the actual copied basis from state4/candidate14: remove original labels5,9,11 (mask2592), retain the other9 original labels, and add two labels carrying signal20. It has11 labels with the two identical signal20 occurrences preserved. The independently checked vertex8=0 pool cut excludes raw Runs of every size≤11 (15+constant1>11+paid4). The forest theorem therefore excludes every actual Live state with deficit≤1 equipped with a ReadOnce partition over this copied basis. This concretely validates an arbitrary positive-depth cofactor leaf. Source `lemmas/State4ReadOnceForest.lean`, SHA256776cd1f2bafd8dcd9bf3e1050d1ed76f654492a906d8912db7da684abbaf8572,13977bytes; EXIT0 and complete output archived. The original state4 budget13 has depth2 and first copying this3-leaf entry gives precisely this11-root/budget11/depth1 basis. Full-gap and intermediate-double-copy tree integration remain unproved.

## proof_structure completed subtree126663 (2026-11-25T14:27:58.305758+00:00)

The generic finite successor checker and cofactor checker are checked. `Expansion126663Conditional.lean` validates180cofactor certificates in23blocks and all1440ordered branches in10operand blocks, covering720distinct children (180cofactor +540row rejects from74witnesses). `Expansion126663.lean` discharges all14Slice hypotheses with checked constructors, proves `completed_subtree : Impossible true graph12 rawState.toFinset`, and derives `frontier_lower_thirteen`. The frontier is all original inputs exceptx4 plus `!x4 && (x0 || x1 || x2 || x3 || x9)`. This is one completed nontrivial subtree of the signed17 OR-edge search, not the entire initial case or posted gap. Append-only combined source: `Subtree126663Extension.txt`; no main-target edit or git write was made by proof_structure.

### status_review update 2026-11-25 14:30 UTC

- FirstCopyRun and CopyInputPartition both compiled and were independently reviewed by counterexample. The first constructs the deliberate duplicate-a list Run in k+1 gates; the second partitions the indexed state into a fresh true-copy label, retained false-copy label and unchanged lifted labels. They support an intermediate cut while retaining both gate operands.
- IndexedForest and the unconditional Expansion126663 wrapper/combined extension independently reviewed. The latter establishes one signed cap12 frontier exclusion and Lower13; it is a completed kernel-checked subtree, not the whole gap.
- Signed17 OR-nonedge independent replay completed:440569 nodes,248807 cofactor witnesses,183776 row witnesses,5653 memo isomorphisms,440568 enumerated child cases; all445 root branches closed. The full compressed archive and verification sources/logs are preserved. Formula leaves and remaining cofactor profile instances still need kernel certificates.

### Counterexample / intermediate first-copy cofactor soundness (2026-11-25 14:31:21 UTC)

`first_copy_forest_exclusion` now compiles. In an actual double-retention step with tail cost k, it copies the retained a-support, indexes its second copy by the fresh output signature z, and uses the actual pre-binary Run of k+1 gates. The indexed ReadOnce forest then contradicts any copied-basis bounded-Run cut at depth d under k+1≤|U|+d. Two equal a values keep distinct leaf labels; all other formulas relabel through Sum.inl. No finite Cert2 bridge/column condition is needed: original ReadOnce wire provenance supplies the formulas directly. This closes the earlier first-successor cofactor-leaf gap before a second copy is taken. Source `lemmas/IntermediateCopyCut.lean`, SHA256acc521f908285615caa02a59d67ddab85cbab894f4bd6914d9362b829d97bef4; EXIT0 with full log archived. Complete integration into a cofactor-aware tower and closure-entry pruning are still separate obligations, not claimed here.

### Counterexample / closure-entry cofactor cut bridge (2026-11-25 14:36:32 UTC)

`compressed_wire_forest_exclusion` now compiles. For any actual live state and ReadOnce partition, replace one current wire z’s entire support A by one singleton root carrying z; all other formulas lift unchanged. The checked forest then contradicts any bounded-Run cofactor cut on the outside-A-plus-z basis. This is precisely the local partial-substitution soundness needed by copy_search_pruned.py’s closure-entry pruning. The budget is stated using the actual compressed basis cardinal, so no informal paid-gate credit is assumed. Source `lemmas/CompressedWireCut.lean`, SHA256d933f1f320c8933bcd0115ad82f055341d56c8f319b3638fdfa1c0885ebfe753; EXIT0, full output archived. Together with whole-forest and intermediate-first-copy cuts, the local semantic obligations are now available. A unified cofactor-aware recursive certificate checker and a complete certificate for the gap are still not supplied.

## proof_structure: compressed checked subtree126663 (2026-11-25T14:37:10+00:00)

The original 193-word registry has been replaced by 10 input columns, 5 prefix bin expressions, and 178 bin expressions on the 10 frontier roots. All 197632 truth-table bits match independently, and Lean proved exact list equality. The compact replay and final unconditional wrapper both compile with exit0; full logs are archived. The append-only package `lemmas/Subtree126663CompactExtension.txt` is59138bytes (104656 before), SHA256 `1e0ceb5f11a2d53a9fb231eaab59efedc87f03e3763846184ea2bbe5848ab9eb`. Conditional replay took174.059seconds and wrapper3.511seconds. It proves the actual completed subtree Impossible at12 and Lower13, with all14 cofactor bounds supplied. It does not prove the full signed17 first-OR case. Original checked sources remain unchanged.

### finite_invariants: reconstructed adjacent-OR rectangle bound, 2026-11-25

PR8827 contains only a reduction whose tree bound is a hypothesis; its separately claimed rectangle proof was not published in that commit. Independently reconstructed and Lean-checked `RectangleOrEdge.adjacent_or_formula_lower`: any positive de Morgan formula on the ten original Petersen inputs plus a freely reusable x0 OR x1 input, computing the Petersen edge function, has at least 20 leaves. Integer 15-by-15 rectangle weights have total 79; every permitted leaf rectangle has weight at most 4. Formula induction partitions rows or columns exactly, so negative weights are sound. Source/log: `RectangleOrEdge.lean` and `.compile.txt`. This proves the adjacent-OR monotone-formula subcase only; it assumes no general circuit/star normalization and does not cover arbitrary signed terminal banks.

### Rectangle binary prefixes — finite_invariants
Three additional Defs-only exact integer rectangle certificates compiled EXIT0, empty log: RectangleBinaryPrefixes.lean. Positive formulas with freely reused ten inputs plus adjacent AND, nonadjacent AND, or nonadjacent OR each require20 leaves. Matrix totals117/6,40/2,231/12 all exceed19. The positive-support selector handles an empty first-gate support safely by filtering positions. No circuit normalization is claimed. Independent review requested.

### 2026-11-25T14:43:39.573527+00:00 lean_setup compression feasibility
No large numeric token repeats; literal factoring cannot help. Exact elaborated dependency closure preserves essentially all signed certificates for both baseline17/18 and all current cofactor consumers. Deletion-only candidate saves7831bytes; corrected full build is running.
WidthPrototype is checked and independently reviewed:741lines generalize the entire pre-input foundation to BitVec(width+1). WidthSpecialization is also checked/reviewed, proving16 defining equalities and6 Live/Reach/Run equivalences to the original512/1024 versions. No target changes. Generic-source and compatibility overhead means realistic combined helpers remain~290–310KB; report is compression-report.txt. This does not solve the large search-DAG certificate budget.

## library_route: pruned-copy fixture and format study

The complete signed-17 OR-edge and OR-nonedge computations are independently audited and archived, but their complete Lean certificates and the original target remain unproved. The compact OR-edge format study estimates a 58,380-byte binary skeleton, excluding all formula certificates and Lean helpers; see search/certificate-format.

A new indexed-label pruned-copy fixture has 14 nodes, 269 retained entries, 40 subtree cuts, and 2 bridge cuts. All cuts use only checked single-zero lower 15. The unified checker agents have the interface; independent finite-data audit is pending. A bounded optimized monotone-19 root run reached 41,908 visits in 60 seconds and remained unfinished. Source, complete log, and fixture are in search/pruned-copy.

2026-11-25T14:46:28.410320+00:00 lean_setup: NineSignedPruned full build EXIT0,181warnings0errors;239198bytes (7831saved), all retained blocks unchanged. Compression feasibility artifacts and specialization evidence are reviewed. CompressedIndexedForest (38lines,1876bytes) also compiled EXIT0/empty log, giving the requested indexed-value compression step for pruned bridge cuts; counterexample is reviewing. No active builds remain from lean_setup.

### First-NOT rectangle certificate — finite_invariants
RectangleNot.lean compiled EXIT0 with empty log. Positive formulas over ten inputs plus freely reused NOT x0 require at least20 leaves. Enlarged matrix uses21 positive and17 negative rows, total2439, leaf rectangle cap128; exact kernel checks verify every allowed support subset, maximum support12. Alongside RectangleOrEdge and RectangleBinaryPrefixes, this reconstructs all five representative first-prefix monotone formula cases claimed but not published by PR8827. These are restricted formula theorems, not arbitrary circuit lower bounds and not signed terminal-bank exclusions. SHA256 ebe9484f3e16e28703a550c562dfe3e95dc22cfe17336f50d1c604a937bd1baf. Independent review requested.

### Actual mono19 tight banks — finite_invariants
Fixed checked matrices exclude none of the8 largest pure-input20-root banks; the best gives equality40=20*2. Across41 exported banks only already-cheap node39189 is excluded. A subsequent bank-specific positive rectangle LP succeeds on all8 large banks. Exact integer conversion and independent full subset maximization give positive gaps12,31,13,31,13,15,47,14 at denominators12,24,12,24,12,12,36,12 for nodes41908,37639,34847,3563,35467,10286,34846,34845. Full integer matrices, ten input costs and multiplicities are saved in rectangle-mono19-tailored-exact.json. These candidates are computationally checked but not yet Lean-certified. Root prioritizes a generic tight positive Run measure bridge, which also applies existing uniform prefix certificates to ≤19-root banks after the first gate.

## Root re-plan after the two-hour checkpoint

The7674-line named partial builds. Both signed17 first-OR computational cases are complete and independently audited; one real Lower13 subtree and its45.5KB certificate compression are kernel-checked. The exact posted theorem remains absent. No signed18 or general zero/one-NOT exclusion is claimed.

Finish the real14-node pruned-copy fixture through the general actual-Live soundness theorem. Its finite entry/bridge checks and42 cofactor cuts now compile; local semantic lemmas alone do not certify the whole recursive search. Counterexample owns recursive soundness, proof_structure owns concrete finite replay.

For the original zero-NOT branch, begin the computational case after a canonical first binary gate. Checked operand retention supplies all ten inputs plus that gate, budget18 and deficit8. The existing20-leaf rectangle certificates can exclude tight banks of at most19 roots drawn from those11 free functions, including duplicates. finite_invariants owns the tight-Run measure bridge; library_route measures actual effects. Bank-specific LPs also separate the8 previously expensive pure-input banks, but those numerical candidates still need exact certificate integration.

Certificate source size remains a barrier. The literal skeleton estimates exclude formula certificates and decoder proofs. Safe pruning, width sharing and metadata-based identifier shortening save tens ofKB, not100KB individually. Preserve exact original sources and reversible maps; do not imply the512KiB full proof already exists.

## proof_structure: finite pruned-copy fixture (2026-11-25T14:57:03+00:00)

The exact state0 fixture now has a checked `PrunedCopyFixture0.completedPrunedNode` at depth1. It covers14 nodes,269 table entries,42 cofactor cuts (40 omitted-entry and2 bridge),13 copy-child bridges, and13 depth0 child nodes. All source data preserve duplicate labels. The42 cuts use only checked zero-cofactor lower15. Generic finite entry/gate/bridge checkers, singleton partition adapter, and pair-column semantics are checked; the actual initial root has12 distinct signatures and12 labels. Source/logs are archived under lemmas/PrunedCopyFixture0{Cuts,Tables,Node,Initial} and helper names. Table compilation took99.667seconds. This is a recurrence certificate only until counterexample proves its general implication to actual Live exclusion; that theorem is the remaining dependency.

### counterexample: unified pruned-copy soundness (2026-11-25T14:57:49.832359+00:00)
PrunedSound now compiles EXIT0 with empty output. General arbitrary-depth PrunedNode soundness includes all three cofactor pruning forms: whole copied bases, generated compressed entries, and compressed bridge entries. Gate-count induction preserves actual-Live partition, ReadOnce provenance, and column support; duplicate signatures are indexed separately. The concrete 14-node fixture is checked by proof_structure and awaits this final theorem application. Full target remains open. Immutable PrunedSound SHA256 0dc3cbf6560ca69f726795f0eaa7b37268991fdcfe7c33ce78ae519630383f4b.

### Tight positive Run rectangle bridge — finite_invariants
RectangleRun.lean compiled EXIT0. Generic run_length_le and run_tight_measure prove any subadditive integer wire measure cannot increase along a tight Run, with list multiplicity preserved. A maximum signed rectangle measure is subadditive under positive AND/OR by exact disjoint partitions. tight_run_bound and tight_run_uniform expose the bound for arbitrary finite samples and integer matrices. No circuit normalization, complements or sharing beyond the Run tightness condition is assumed. SHA256 642aa3a2a10a90775e4cee820b5a1936fc4ddb770d3d1b7799def46ec2d34e00.

### Concrete first-OR Run exclusion — finite_invariants
RectangleOrEdgeRun.lean compiled EXIT0 with empty log. tight_prefix_exclusion rules out any tight positive Run to Live1024.graph from ≤19 roots chosen with multiplicity from ten inputs and x0 OR x1. It kernel-checks all330 sample/basis correspondences and30 target rows against the exact Live1024 tables, then uses the signed rectangle total79 and per-root cap4. RectangleRunIndexed.lean also compiled EXIT0; it supports nonuniform costs indexed by a list of labels, preserving duplicate occurrences. Both caches are available under scratch finite_invariants.

### proof_structure: actual pruned-copy exclusion completed (2026-11-25T14:59:52+00:00)

`PrunedCopyFixture0Complete.lean` now compiles with exit0 and proves `Impossible false graph 12 (roots0.image nodeRaw0)` without hypotheses, using the independently checked recurrence data and counterexample's general PrunedSound theorem. Final757-byte source SHA256 `b2003cc27a0131d696a775a6caa22fc74f250bb0bc918d705aabf4a262b8eff2`. Both counterexample and status_review independently reviewed the application. `lemmas/PrunedCopyFixture0.build-order.txt` lists all28 archived source dependencies in rebuild order; none is missing. Source total551701bytes before stripping imports or pruning unrelated imported examples. This is a real completed nontrivial search fixture, not the full gap or full initial search case.

### Actual20-root bank exclusion — finite_invariants
RectangleBank41908.lean compiled EXIT0, empty log. It rules out the actual largest mono19 pure-input bottleneck bank with multiplicities[3,2,3,2,1,2,2,1,2,2] and19 remaining gates. The225 integer weights total116; exact per-input maxima[0,0,0,8,12,8,6,12,6,12] sum104 across the20 root occurrences. All80 input-support subsets are kernel-checked. The indexed Run measure bridge gives contradiction116≤104. SHA256 a00dd72a9786d235c718a8ce185dee2261c788d255bb6040e55f07d6e2963428.

### 2026-11-25T15:03:31.590329+00:00 lean_setup metadata compression / checker transfer
NamesCompressed full build EXIT0 (201warnings0errors), exact19721-byte saving from353344 to333623bytes. .ilean-directed edits affect683 internal helper names at3863 constant-name spans, preserving47 public/namespace endpoints. Fresh names and exact forward/inverse expansion independently verified. Source/log/map/audit archived; active target unchanged.
SharingReadOnce and PrunedSingleTransfer are checked and independently reviewed; PrunedSound and the completed fixture0 final application also received independent full-source/interface reviews. No active builds remain from lean_setup.

Rectangle fixture 0: replaced all thirteen cofactor child certificates by a common checked Tailored10286 rectangle matrix. Cached root wrapper and complete standalone both compiled with exit 0. Standalone source is 189314 bytes / 3679 lines, SHA256 80e5c89cf6a0c46bc82a11fbf2a1937728b82b0a6acd3bf233017f165871efe5, only PEqualNP.Defs imported. This is the existing twelve-root/budget-twelve branch, not the full gap. No NineSigned/cofactor declarations are required. Exact assembly manifest and source budget archived; independent assembly review pending.

### counterexample: independent-set canonicalization (2026-11-25T15:19:38.945705+00:00)
Independent exhaustive graph-automorphism enumeration confirms120automorphisms,76independentsets, six orbit sizes1,10,30,20,10,5. Lean IndependentOrbits canonicalize/nonempty_canonicalize both compile with empty log, 5195bytes. The certificate covers every independent Finset and validates actual bijective adjacency-preserving witnesses to the six posted representatives; it separates the empty set. No star normal form, eligible-reservation bound, or circuit surplus theorem is assumed or established. SHA256 d0d1762786f2721c7ec753d2d4a880d9adacbd1042af708000b33eb621d32e63.

Root re-plan at 2026-11-25T15:21:32.440179+00:00
- Preserve original task: exact L-meta-2373 still unproved; current named partial builds, latest full checker remains REJECTED(no-theorem). No completed proof/refutation/PR submission by this agent.
- Concrete certificate path improved: rectangle-only fixture compiles self-contained at189314B, replacing the old551701B dependency union. This excludes exactly one12-root/budget12 state, not a firstgate case. Backed up in5d52f71f7a9699c44b2d085809322452e59070e3.
- Library route: weighted13-matrix mono19 first-OR-edge search remains inside its first copy branch after524552visits/180s. New completed-only memo checkpoints are reviewed; one20-minute attempt now runs with atomic snapshots and profile/reset diagnostics. No interrupted root is marked excluded.
- Finite lane:23585-profile scale remains a source-budget problem; smaller-side rectangle checker is compiled/reviewed, with an actual20-profile benchmark underway. Dominance compression helps but does not yet give a complete small firstgate certificate.
- Signed/cofactor lane: existing exact monotone9lower16 certificate is being kernel-replayed. Computational searches already used16; this closes a proof dependency, not a new pruning improvement. It currently adds~284KB before pruning.
- Counterexample lane: exactly-one-NOT local SAT has100localUNSAT neighborhoods,0UNKNOWN, no global conclusion. A new300-second signed18 first-AND-edge exact search is authorized after15:21:07renewal; no old memo cache,1GB/oneCPU limit. Any found circuit still requires minimal-NOT accounting and Lean validation.
- Structural lane: acceptedHeawood core transfers only its generic hypotheses; its numerical closure is vacuous forPetersen. Six independent-set orbits are kernel-certified. A bounded investigation of the all-eligible/no-residual corner may yield a new semantic argument; singleton support is not assumed to imply exact input truth.
- Public PR15214 was opened by another process from the stale98-line partial and lacks the required theorem. It is not an accepted proof; no other branch or lease was touched. Current source and reports remain explicitly partial.

Fresh signed18 first-AND-edge search (2026-11-25 15:21:17–15:26:17 UTC): unchanged reviewed live_search_resume, no resume cache, one CPU and 1GB address-space cap. Stopped at the ordinary 300-second limit after 446,597 nodes; no circuit found, five open nodes including root. Peak RSS 210,432 KiB. Complete trace/logs and 6,148 completed-only continuation states archived under search/signed18-and-edge. Independent streaming replay checked every recorded transition and signed row witness plus matching remaining budgets on memo links. Cofactor/formula/memo-symmetry certificates were not rechecked here. No UNSAT or Lean claim.

### Whole-search rectangle cost feasibility — finite_invariants
The completed180-second search trace remains incomplete as a whole case. It emitted374,385 rectangle cuts with32,868 matrix/signal costs, reducing to23,585 sampled profiles. Same-cost observed-mask dominance leaves13,866 nontrivial profile certificates and461,012 smaller-side subsets; grouped packed literals occupy151,395 bytes. Greedy mask inflation leaves11,081 records and126,254 bytes but increases checks to1,574,282 subsets.
The first Finset.powerset20-profile benchmark was deliberately terminated at53.6s and approximately8.9GB RSS to protect another long proof. Generic RectangleMaskCheck soundness did compile and pass independent review. A pure List recursive checker with a packed Nat matrix then checked20 actual profiles/2,560 subsets in7.71s at3.61GB peak RSS (Defs import baseline3.14s/2.88GB). Its source/log are archived as RectanglePackedBenchmark20; the general fast-path soundness bridge is being proved by status_review. Based on this small sample, the observed-maximal table should take roughly15–20 minutes of kernel work in bounded batches, plus generic code and matrix definitions; no full table build has started. These are estimates for the partial trace only, not a whole-case completeness claim.

PositiveTailExtraction: checked public arbitrary-bank extractor for a legal NOT-free gate tail. Given proper target membership in execute gs w, obtains Live false target k S with k≤gs.length and S⊆w. Archived 6,231-byte source and empty EXIT0 log; six private helper blocks are byte-identical to Count, with comparison map retained. This supports proof_structure’s ordered first-AND/NOT prefix case. Independent review requested from that consumer.

### library_route resource checkpoint 2026-11-25T15:33:36.014442+00:00

The mono19 first-OR-edge copied-input orbit containing x0/x1 is computationally excluded; the second orbit remains open. At 735 seconds the original checkpoint run reached 976213 visits and 52141 sparse closures, but persistent signal-vector growth drove total estimated memory above the projection-reset threshold. This caused repeated cache clearing even when little clearable cache remained. Parent authorized stopping CPU work; SIGSTOP preserves the old in-memory terminal dictionary until its wall deadline permits a normal footer exit. The immutable paused checkpoint holds 52200 completed exclusions and no active root key.

A monotone-only Cov4 variant preserves all 225 row columns, rejects signed mode before initialization, and reproduces the 3000 visit smoke and completed memo byte-for-byte. A further resource-only variant adds 180 MB minimum clearable cache hysteresis and 1.5 GB total guard. It also passes 936 rectangle self-tests and identical smoke; independent reviews passed for the hysteresis change. The optimized continuation is running from the immutable completed checkpoint, with separate logs and atomic snapshots. No whole mono19 first-gate case or full L-meta-2373 theorem is claimed.

### proof_structure: concrete ordered AND–NOT exclusion

The new checked `Live1024.OneNotFirstAnd.ordered_circuit_lower` establishes20≤C.size whenever C is fan-in-two, computes the exact Petersen edge function, begins with AND of distinct original inputs a,b then NOT of wire10, and has no later NOT. This statement allows either prefix result to be unused. `LiftSeventeen.monotone_rt_lower` supplies18binary gates for a positive input-root computation; the free-bank lower uses the retained input plus the constant AND or NOT value after a=0 to charge two constants above the checked mono9 lower16. `PositiveTailExtraction` turns the actual ordinary tail into a Live run with k≤tail.length and roots contained in the exact evaluated prefix bank. All three compile EXIT0. The original6071-byte bank lemma remains unchanged; new wrappers remove its used-wire condition explicitly. Full artifacts/logs are in results/orch/lemmas. Exact-prefix result only; arbitrary one-NOT circuits and first-OR→NOT remain open.

### proof_structure: AND–NOT exclusion at arbitrary locations

`Live1024.OneNotFirstAnd.anywhere_circuit_lower` now handles C.gates=pre++[AND(a,b)]++mid++[NOT(10+pre.length)]++post, with a≠b and every gate in pre/mid/post nonNOT. FanInTwo and exact Petersen computation imply20≤C.size. `FreeBank.pull_positive_chunk` extracts backward using gv on the original execution list, while adding h and neg h only to the membership bank; default/out-of-range wire reads therefore remain unchanged. Actual prefix preservation and exact stored-slot lookup prove the two free gate values. The three charged segment lengths sum to size−2. Both modules compile EXIT0 with empty output; forbidden source-fragment scan passes. Combined endpoint axiom audit uses only propext, Classical.choice and Quot.sound. Independent helper/consumer reviews requested.

Updated 2026-11-25T15:43:42.438969+00:00
### Finite invariants: dynamic rectangle cuts and symmetry reuse

- Automated grouped-profile LP plus integer reconstruction now excludes all 119 frozen second-copy diagnostic banks in 34.7 seconds (54 new integer matrices and six existing dynamic seeds). These are research cuts, not a complete whole-case certificate. V2 matrices have not yet received independent audit.
- A better result uses the original 13 matrices: all 119 banks fail under some Petersen automorphism, versus zero in their raw orientation. Exact subset enumeration takes 0.61 seconds with 595 profiles per matrix.
- Seven transformed sample-row variants cover all 119 banks; they reuse four original weight arrays. The selected data are in finite_invariants/dynamic-symmetry-selected-v1/matrices.json under the job scratch root. Counterexample is independently auditing before publication. Direct transformed sample labels avoid adding any permutation assumption to the rectangle checker.
- The first six independently audited DynamicV1 matrices are already published atomically at finite_invariants/dynamic-loader/rectangles.txt, IDs 1001–1006. Append-only invariant will be preserved.
- The generated 13,866-region full Lean replay remains uncompiled (261,359 bytes, 614 chunks, 461,012 smaller-side subsets). Root prioritized closing the computational first-gate case before spending kernel time on this incomplete trace.

### counterexample: selected symmetry matrix audit 2026-11-25T15:44:58.623468+00:00

Seven explicitly transformed old matrices independently exclude all119 frozen dynamic-cross-v1 banks. Exact signed integer audit recomputed833 matrix/bank combinations and406 distinct support profiles, preserving every duplicate occurrence;305 positive cuts and every claimed coverage/margin agree. All seven permutations preserve the Petersen graph and full1024-row target; transformed samples match the documented bit convention. Complete immutable sources/inputs/logs/results are in `results/orch/rectangle-cut-audits/symmetry-selected-v1/`, REVIEW SHA0b6e8c873ec5f6f6d771853a69bd271da21617c436f068e8f9b2669b6ada8125. This validates computational cuts only; whole-case exhaustion and Lean certificates remain separate. New54 V2 LP matrices were superseded for this batch and have not been independently audited.

Also independently reviewed `FreeBankExtraction.lean` SHA7aa500427f2c9bd37fdd1b790a2f07529f2d3c0c02c105bbddb74e5d08eb5d15: exact old prefix plus three sound free-root helpers, original execution index semantics preserved; report `review-free-bank-extraction.txt`.

### proof_structure: arbitrary negated value forcing two inputs

`Live1024.OneNotForcedPair.circuit_lower` now allows any actual gate value h with semantic premise `forcesPair h a b`: on every truth-table row, h=true implies both distinct original inputs a,b=true. An earlier arbitrary gate g must evaluate to h at its actual execution point; the later designated NOT reads wire10+pre.length. With pre/mid/post positive and exact Petersen output,20≤C.size. The producing gate itself need not be positive for this stronger theorem, so the ordinary sole-NOT case is included. Retention of a uses the checked conditional influence witness holding b=false, making h and neg h equal on both rows. The a=0cofactor then gives two distinct constant frontier roots above the mono9 lower16. Both extra outputs being unused are covered by the checked mono18bound. Source8072bytes, EXIT0 empty output, format scan clear, axiom audit only standard three axioms; independent review requested.

### counterexample: dynamic matrix audit completion 2026-11-25T15:49:36.450968+00:00

Preserved exact audits for second symmetry batch13×117 (101covered), nine transformed newweights×16 (13covered), and three fresh matrices×16 (final3covered). A direct51×216 run independently confirmed all216 frozen banks covered (11016comparisons,3876profiles); archive `rectangle-cut-audits/all216-v4/`, reviewc104a03a…. Final optional five transformed matrices cover all21 third-snapshot residuals and are archived separately in `symmetry-selected-v3/`. Library reports the actual first-OR-edge computational completion used onlyIDs1001–1026; later batches are not dependencies of that run. No matrix audit is itself a Lean certificate or proof of whole search soundness.

Root re-plan at 2026-11-25T15:55:51.700860+00:00
The strong-cofactor monotone19 first-OR-edge computational case closed; preserve its full linked traces and completed-only caches, then export a fresh fixed-matrix proof DAG. Raw memo absence assertions are not Lean certificates. A fresh weak15 run reached734033nodes in300.55seconds without a witness or a completed-case verdict. The new four-gate conditional bridge may eliminate the277KB mono16 dependency once Petersen mono20 is independently proved. All other first-gate cases and unrestricted one/two-NOT cases remain unresolved. Counterexample studies negated functions forcing at most one input; proof_structure studies exactly-two-NOT equality; finite_invariants measures real profile union and library_route exports finite witnesses. No new reduction is assumed available because allthree slots were occupied. Archive reviewed compiled partials immediately.

Fresh weak15 mono19 first-OR-edge benchmark (15:48:14–15:53:15 UTC) stopped at its300-second allowance after734,033nodes, with26,439completed weak-mode memo states and no full-case verdict. All1,145cofactor bounds were independently compared to the signed table and match. Full outputs/traces/cache archived under search/weak15-mono19-or-edge; audit confirms root absent and replays164sampled bank histories. Parent then authorized a600-second continuation using only this weak memo and immutable reviewed V3 matrices; no stronger-mode cache is used.

Research checkpoint 2026-11-25T16:01:30.447136+00:00: full strong-cofactor first-OR-edge computational case independently audited. Archive33files/25.57MB plus original11files/13.43MB includes exact memo chain67→52200→55426→59744→113408 and allfive complete trace dictionaries.1,411,154 rectangle events jointly deduplicate to62,349costprofiles; exact cost recomputation passes. These are not a Lean proof DAG. Separate signed18-ANDedge timeout, dynamic loader, matrix generation/audits, and explicitly limited structural research are preserved. GitHub transient commit_refs_rules error on prior checkpoint resolved by expected-old-SHA guarded fast-forward retry; noauthenticationfailure.
