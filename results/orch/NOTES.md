L-meta-2592 orchestration notes

Only root calls the desk, commits, pushes, or opens a PR.
Lease obtained 2026-11-25T13:44:05.796Z; renewed at 13:45:51 UTC, expires 14:05:51 UTC.
Exact statement: /tmp/oec/pequalnp-pilot-93/statement.txt
Main proof target: lean/PEqualNP/Outside/L_meta_2592.lean
Allowed project imports: PEqualNP.Defs only. No sorry, axioms, or native_decide in results.
Append findings with strategy name and UTC time. Agents own separate scratch files under results/orch/lemmas or /tmp/oec/pequalnp-pilot-93. Never edit another agent file.
Reductions open, but desk reports reductions_live=3 (capacity full).

2026-11-25T13:48:22.280644+00:00 counterexample_search: Petersen truth table has 76 false inputs and 5 maximum independent sets of size 4. C++ full-truth-table CGP search is running from 20-gate cover constructions, deleting one gate and allowing AND/OR/NOT mutations; no exact 19-gate witness so far. Source and complete log in /tmp/oec/pequalnp-pilot-93/search_cgp.cpp and search_cgp.log.

Structural strategy, timestamp corrected at 2026-11-25T13:50:40 UTC: Found checked L_meta_4725 (146284 bytes / 3224 lines), exact binary floor 15 + notCount C <= C.size for Petersen edge function. Proof uses six necessary branch wires plus input count. This rules out >=5 NOT gates at budget19; 1–4 NOT remain. Extracted namespace-renamed partial to results/orch/lemmas/Structural.lean, awaiting Lean toolchain. finite_certificate owns first-gate dependency map; reduction_routes owns fewNot R4727 map.

Root 13:48 UTC: Lean v4.36.0 installed locally under /tmp/oec/pequalnp-pilot-93/elan. Use PATH=/tmp/oec/pequalnp-pilot-93/elan/bin:$PATH ELAN_HOME=/tmp/oec/pequalnp-pilot-93/elan. Mathlib cache get in progress; wait for root before builds.

2026-11-25T13:49:24.868282+00:00 reduction_routes: examined all R2592 and R4727 cuts. R4727_17 compile completed L6060 but lower bound L6062 still conjecture; R4727_53 signed compile completed L7227 but signedBound L7229 still conjecture. No closed assembly via either route. Wrote generic last-NOT factorization candidate results/orch/lemmas/Reduction.lean, awaiting cache for Lean validation.

2026-11-25T13:49:42.361116+00:00 finite_certificate: R651_1 first-gate branches L1884/L1886/L1888/L1890 remain unproved. Nonedge-OR normalized cases L5236 (3–4 NOT) and L5238 (>=5 NOT) are checked, but L5234 (1–2 NOT) and L5232 (monotone) remain open. Found Lean-bundled cadical; generated 30-row weak circuit CNF (15 minimal true + 15 maximal false), 139710 clauses, waiting root renewal before search.

2026-11-25T13:50:40.738267+00:00 structural: Added largeNotImpossible for >=5 NOT; file 146975 bytes, 3239 lines. Format string scans no forbidden root identifier, quotes, sorry, axiom, or native_decide. Binary floor core proves six needed first-branch groups and counts 10 inputs+6 branch slots−1=15 binary gates. Strengthening requires additional graph-sensitive branching beyond vertex-cover/twin-group argument.

2026-11-25T13:52:09.146498+00:00 counterexample_search: Unconstrained 19-gate search reached exactly 5 false-positive rows by computing Petersen plus nonedge {5,6}; no witness. Forced-output-reachable-NOT search reached 15 errors. Independently generated and exhaustively checked an exact 20-gate monotone circuit on all 1024 rows, stored in /tmp/oec/pequalnp-pilot-93/petersen_upper20.json. Search heuristic is not exhaustive and proves no lower bound.

2026-11-25T13:53:03.491248+00:00 reduction_routes: results/orch/lemmas/Reduction.lean compiled with sole import PEqualNP.Defs, exit 0 and empty compiler output. 98 lines frozen for checkpoint. Proves generic last-NOT cut exactly (the first hypothesis of R2592_318), preserving all gates and semantics even for empty/invalid NOT operands. Full log /tmp/oec/pequalnp-pilot-93/reduction-final-build.txt.

2026-11-25T13:56:20.400635+00:00 finite_certificate: Finite.lean passes lake env lean (coverage2 stdout/stderr empty, exit0). Kernel-checked76 false rows; selected30 rows distinct/bounded; coverage gives finite_rows_complete for any inclusion-monotone Boolean function. SAT30-row exactly1NOT solved SAT33s but was an antitone separator, wrong on many untested rows. All-types30-row SAT likewise spurious. Exactly1NOT92-row (all76false+15edges+1023) search running300s cap; full1024 exactly3NOT CNF prepared with1,433,488clauses (32.1MB) for nextrenewal.

2026-11-25T13:56:28.426066+00:00 structural: Structural.lean compiled successfully (exit0), full warnings-only log /tmp/oec/pequalnp-pilot-93/structural-build.log. Structural16.lean wraps existing L5236 signed certificate to get global16binary floor and exclude>=4NOT; global16floor is also already checked as L6581. Compiling Structural16 with scratcholean. Retention.lean builds finite400case certificate that the first binary gate must retain one input operand; reduction_routes handles restriction charging2 and automorphisms toward17binary floor.

2026-11-25T13:57:35.249249+00:00 counterexample_search: 19-gate monotone near-candidate improved to 4 errors, exclusively maximal independent triples {1,3,7}, {0,7,8}, {0,3,9}, {1,8,9}. This is a monotone overapproximation, NOT a counterexample. Candidate is latest BEST 4 in search_cgp.log. Exhaustive two-gate rewrite windows inserting a NOT are running; no witness.

2026-11-25T14:03:07.617393+00:00 structural: RetentionStandalone.lean (71312bytes) compiled exit0; companion Retention.lean alsoexit0. New first_both_retained proves both firstbinaryoperands staylive, using400finite witnesscases checked by kernel. Circuit extraction realizes original10pins. Root notified forindependentreview+push. Structural16fullsignedcertificate remainscompiling withoutreportederrors.

2026-11-25T14:05:47.740611+00:00 counterexample_search: All 21 restricted SAT repair windows were UNSAT on all1024 input rows (not an unrestricted lower bound). Exhausted 1,393,536 single-consumer rewrites after inserting oneNOT into the18-gate near-circuit, and 8,275,134 two-consumer beam rewrites: no improvement below4errors. Forced-active-NOT CGP finished600seconds /1,483,600,000 mutations, best8errors. Complete computational report and source hashes: /tmp/oec/pequalnp-pilot-93/counterexample-search-report.json. Unconstrained20minute CGP stillrunning.

2026-11-25T14:06:06.101523+00:00 structural: Full Structural16.lean compiled successfully (exit0), wrappers provide 16 + notCount C <= size and exclude >=4 NOT. Full source285634bytes; log /tmp/oec/pequalnp-pilot-93/structural16-build.log. Retention companion recompiled against full Structural16.olean; independent review underway. New floor17 proof is being assembled by reduction_routes from both-operand retention plus a zero-input restriction.

2026-11-25T14:08:35.636631+00:00 counterexample_search: After root renewed the lease, started a fresh 20-minute search with exactly two active NOT gates. Sources and output are now written directly to results/orch/search/ so they survive checkpoints. Complete earlier computational evidence has also been copied there; none is a Lean-checked lower bound.

2026-11-25T14:09:54.949757+00:00 reduction_routes: full Restriction companion compiled exit0 against full Structural16. Then Floor17Live.lean proved 17 <= k for signed semantic Live runs starting from Petersen inputs; Floor18.lean proved 18 <= k+1 when first normalized binary operation is not OR. Both actual full-module Lean checks exit0 (only unused simp warnings). Standalone Structural17.lean with circuit translation currently compiling.

2026-11-25T14:11:28.394655+00:00 or_first_bound: OrFirst.lean companion kernel-checked via OrFirstPackedTest.lean, exit0, empty stdout/stderr. Packed4000-slot witness table proves retained distinctpin c after firstOR(a,b) followed by any signed binary gate combining OR(a,b) and c (2,880 valid cases). Original list-table proof attempt exited137, packed replacement succeeds. Self-contained OrFirstStandalone.lean prepared with allowed PEqualNP.Defs import, awaiting full compilation. Nine-input15-signed-binary CGP search300s found no exact circuit after1,879,000,000 mutations; best3errors, only heuristic evidence.

2026-11-25T14:11:48.455235+00:00 reduction_routes: full reusable Floor17Live.olean and Floor18.olean emitted under /tmp/oec/pequalnp-pilot-93/, both exit0. First-OR agent notified. Structural17.lean standalone 4984 lines/307046 bytes includes all certificate sources and public exact plain-input extractor; full compile still running.

2026-11-25T14:12:13.954772+00:00 root: latest lease expiry 2026-11-25T14:32:13.496Z; current full lease state in scratch lease-current.json. Only root renews.

2026-11-25T14:14:46.130980+00:00 or_first_bound: OrFirstAlgebra.lean compiled exit0 with empty log; bin identities simplify (a OR b) AND NOT a to b AND NOT a, and or_difference_front moves this second operation before OR or deletes unusedOR. OrFirstFloor.lean compiled against full Floor18 modules, exit0 with empty logs; firstOrDifferenceFloor yields18 binary gates, firstOrDifferenceDropFloor yields19 when initialOR signal is not retained. Exact logs or-first-algebra-olean2, or-first-olean2, or-first-floor2 in scratch. Companions frozen; combined standalone still compiling.

2026-11-25T14:16:31.150513+00:00 root renewal; expires 2026-11-25T14:36:30.611Z.

2026-11-25T14:16:33.858629+00:00 reduction_routes: SecondAnd.lean compiled exit0 (99 lines, one unused simp warning), emits SecondAnd.olean. firstOrSecondAndFloor rules out signed runs with fewer than18 binary gates when first gate is OR and second combines that OR with a distinct input using AND or complement-left AND. It applies the retained-input-and-constant-result projection bound with Reach cost1 for the first OR.

2026-11-25T14:18:39.466937+00:00 reduction_routes: COMPLETE standalone Structural17.lean compiled exit0; source4984lines/307046bytes, sole import PEqualNP.Defs. This proves binaryFloor17: 17+notCount C<=C.size for all fan-in-two Petersen circuits, and threeNotImpossible: no budget19 circuit with>=3NOT computes Petersen. No extra hypotheses beyond the claimed partial statements. Full log /tmp/oec/pequalnp-pilot-93/structural17-build.txt contains inherited warnings only. Root notified for immediate reviewed push.

## 2026-11-25 14:18:42 UTC — finite certificate update

SeededRows.lean compiled with kernel decide and narrow Mathlib.Data.Nat.Bitwise import. It checks that the 13 selected 6-input rows encode the four neighborhood OR seeds, four intermediate ORs, six raw inputs, constants, and the three-pair matching target exactly. Full 114-first-signal three-gate certificate remains running, with no diagnostics so far.

A fresh signed-binary 9-input, 15-gate CNF for the Petersen graph with vertex 9 deleted has 23,610 variables and 498,707 clauses (full 512 rows). A random concrete circuit satisfied every structural and evaluation clause; exactly its 390 incorrect output rows violated the corresponding final unit clauses. Solver run pending parent renewal.

2026-11-25 14:19:07 UTC [structural_proof] OneNotPetersen.lean compiled exit 0: a raw input used only at the unique NOT makes the output antitone in that input, contradicting explicit Petersen witnesses. Next proving that a raw input used only by an AND/OR gate with a distinct raw input also cannot compute Petersen, regardless of other gate operations.

2026-11-25T14:20:54.241054+00:00 or_first_bound: Preferred self-contained OrFirstCore.lean passed Lean, exit 0, empty or-first-core.stdout/stderr. It has 217 lines and 23,045 bytes, sole import PEqualNP.Defs, and contains only the definitions needed for second-gate retention and OR/difference commutation. The redundant 301KB full-prefix standalone build was canceled with exit 130; its log is not a success record. OrFirstCore, OrFirst, OrFirstAlgebra and OrFirstFloor are frozen checked artifacts.

## 2026-11-25 14:24:13 UTC — seeded semantic bridge compiled

SeededSemantics.lean compiled with exit0 and empty stdout/stderr. It proves signature agreement respects AND, OR, and NOT; all generated signatures stay below8192; agreement with the matching target implies signature30; and the three-gate Boolean certificate implies no three generated signals compute that matching on the13 selected rows. This file assumes the explicit certificate proposition; the closed114-case certificate in SeededMatch.lean is still checking.

## 2026-11-25 14:28:20 UTC — optimized incremental certificate

The original SeededMatch.lean114-case run was deliberately stopped with SIGTERM after15minutes, no diagnostics, and is NOT a checked full certificate. FastSeededZero.lean in results/orch/finite is checked (6.00s wall, exit0). It contains proved generic incremental-safety lemmas and the optimized firstcase0. Full FastSeededMatch.lean has114 optimized cases assembled but awaits parent renewal and checking. Optimization checks only pairs involving the newly added signal, reusing proved safety of the old bank.

Signed9/15 full512-row SAT timed out at300.14s wall/201.78s CPU,155.62MB peak, with no verdict. Full logs and source preserved in results/orch/finite.

2026-11-25T14:28:51.404377+00:00 or_first_bound: OrTight.lean and allowed-import OrTightCore.lean compiled exit 0; companion logs are empty, standalone stdout contains inherited if_pos/if_neg deprecation warnings, stderr is empty. Complete logs: or-tight.stdout/stderr and or-tight-core.stdout/stderr. Generic tight_constant_step: at a constant-consuming projected gate with total reachable budget L+1, every constant operand is discarded and the result stays nonconstant; false-left permits only OR or complement-left AND, false-right permits only OR or complement-right AND. These are local equal-budget constraints; a whole-run incidence bridge is next. Original nineFloor derives solely from packed cap14 search, exporting no equality characterization.

2026-11-25T14:29:11.146686+00:00 counterexample_search: General two-NOT search and both fixed-input-NOT prefix searches completed without a witness. Final results independently checked on all 1,024 rows and preserved in results/orch/search/search-snapshot-2.json. This remains computational search evidence only.

2026-11-25 14:30:36 UTC [structural_proof] Frozen checked artifacts: OneUseClassified.lean proves sole-reader support-two masks are neutral constants or AND/NAND of an edge; witnesses use independent triples and search only three neighbors. BypassNand.lean proves an actual same-length replacement of AND(i,NAND(edge)) by unary OR(i) when the remaining tail is monotone, since edge=true already forces the target true. Both compiled exit0; complete logs one-use-classified-build.log and bypass-nand-build-3.log in scratch. Reduction_routes owns effective input-slot count and normalization. Remaining challenge: shared computed mask with support≥3, or OR(i,AND(edge)) before the unique NOT.

### 2026-11-25T14:31:00.785082+00:00 reduction_routes: effective input slots
InputSlots.lean compiled exit 0 with empty diagnostics. It proves NOT take-one normalization preserves evaluation, size, and NOT count; effective slot length + NOT count <= 2 size; internal output use costs at least size-1 slots; hence ten essential inputs and live circuit size<=19 with a NOT force an input with exactly one occurrence and a unique gate reader index. Explicit essential/live hypotheses remain; generic dead-gate deletion is next. Frozen SHA256 1c438f2794d4ecc992431b6233c516600a244d6fd6957d6fc1105448e120b413.

2026-11-25T14:31:09.661950+00:00 or_first_bound: OrUses.lean checked exit0 with empty or-uses2.stdout/stderr. CountRun tracks binary gates whose operand satisfies an arbitrary predicate on original semantic wires. counted_projection_lower proves L + selectedGateCount <= initialReachCost + binarySteps if selected wires restrict to constants. Thus Petersen nineFloor15 implies every raw input occurs in at most two binary gates in a tight17 normalized schedule. Actual Circuit syntax/slot bridge not yet assembled.

## 2026-11-25 14:34:53 UTC — full seeded three-gate bound checked

FastSeededMatch.lean compiled successfully: exit0,231.93s wall, empty stdout/stderr. All114 first-signal cases and the closed choices_noThree theorem are kernel-checked. Scope: from the16 fixed signatures (constants, raw6 variables, four3-OR seeds, four intermediate2-OR seeds), no sequence of≤3 additional AND/OR/NOT gates reaches matching signature30 on13 selected rows. This is a restricted architecture result, not the full Petersen gap. Source is frozen for independent review.

Correction: native forest prototype extracts215 restriction columns (the earlier224 was a reading estimate); all768 separation pairs,12 automorphisms, and nonempty/nonconstant domains validated.

2026-11-25T14:36:19.927796+00:00 or_first_bound: RawUses.lean checked exit0 (raw-uses4.stdout one unnecessary-simpa warning; stderr empty). Actual Circuit theorem petersen_read_floor proves 15+count(non-NOT gates whose inputs contain j)<=binaryGateCount. twoNot_raw_reads gives count<=2 for size<=19 and notCount>=2. This handles all permitted fan-in-two cases, unary/empty/duplicate inputs and invalid reads. Generic actual-execution projection core is RawUsesCore.lean, sole PEqualNP.Defs import, no new inductive type.

### 2026-11-25T14:36:30.290263+00:00 reduction_routes: unconditional unique reader
InputStructure.lean standalone CHECKED exit 0, sole PEqualNP.Defs import, SHA256 12e8c3921f258480663544e48ffb72f0ddc157bc7f7bcd24b9bc73a56478b351. It combines InputSlots, Prune, WeightedLive, WeightedPetersen. Generic unread-gate deletion preserves evaluation without strict/backward-read hypotheses, subtracts exactly one gate and its NOT indicator. Minimizing size among equivalent normalized circuits with weight=size+indicator(noNOT) below the original gives a live representative. Explicit finite Petersen witnesses force all10 inputs read. Slot counting then yields an original input with exactly one actual gate reader from the ORIGINAL gap assumptions. The representative is either size<=19 with NOT or monotone size<=18. No live/essential hypotheses remain in normalized_unique_reader. All local instance declarations removed; proof-local letI only. Full build log input-structure-build.txt, olean emitted. This is global applicability for structural_proof sole-reader mask classification, not full contradiction.

2026-11-25T14:37:33.657182+00:00 root re-plan: signed binaryFloor17 is checked and pushed, leaving one/twoNOT and the normalized monotone<=18 case. General CGP and fixed-prefix searches ended without witnesses and are no longer consuming compute. Primary analytic route now uses checked weighted normalization to a live circuit with a sole input reader, then mask classification and gate bypass/deletion. Primary finite route reconstructs the existing signed nine-input forest: cap14 reproduced natively in5.63s; cap15 search running, requiring a Lean certificate before any lower-bound claim. Three restricted sole-reader SAT cases run in parallel as counterexample attempts. Full optimized seeded three-gate certificate passed231.93s; its structural applicability to arbitrary Petersen circuits remains unproved.

### 2026-11-25T14:38:41.275635+00:00 reduction_routes: alias deletion and minimality export
AliasPruneStandalone.lean checked exit0, sole PEqualNP.Defs import, SHA256 1f33da83872b06872a099cd32aeb1beb90fb4f484792d15e4751688d0cadd867. It deletes a gate equal to an earlier wire, redirects all suffix reads and the output, preserves evaluation with arbitrary NOT suffix, fan-in2, exact size decrement, exact NOT-count decrement. MinimumInput.lean companion checked exit0 with empty log and imports clean InputStructureClean; minimal_unique_reader now exposes size minimality among normalized equivalent circuits of no larger weighted budget, for contradiction by bypass plus alias deletion.

2026-11-25T14:40:16.539617+00:00 or_first_bound: Native forest packer results/orch/finite/pack_forest.py generated PackedBaseline.lean from cap14 UNSAT records (1530 states) in0.6s. Packer checks every displacement lookup and all keySet hash collisions; no collisions. Source/layout matches original10-bit prefix decoder and inverse-automorphic linkedSet semantics. PackedBaseline.lean is UNCHECKED: Lean build was not started because root reported lease410. Baseline nodes use maxdepth7 and max18 rules; full packer logs pack-baseline.stdout/stderr.

## 2026-11-25 14:40:19 UTC — lease410 checkpoint pause

Parent reported unexpected HTTP410 despite most recent14:56 expiry. No new builds/searches started. Current cap15 native search is allowed to finish its existing300s cap and will serialize all closed state witnesses. Full FastSeededMatch.lean remains checked/frozen. CompleteSeededMatch.lean is assembled but NOT fully compiled; its isolated abstract bridge check succeeded with empty logs. Current native cap15 stdout/stderr snapshots preserved as live15-running.*; final logs/records will be copied upon timeout/completion.
