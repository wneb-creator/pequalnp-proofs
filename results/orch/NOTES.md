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
