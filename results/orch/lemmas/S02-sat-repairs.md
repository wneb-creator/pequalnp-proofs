# S02 SAT local and distance repairs

Updated 2026-11-24T03:27:09.849836+00:00. Owner: S02/Jason. Read NOTES, INDEX and the available S08 report before this update. Original-CNF performance, preprocessing and cubing belong to S06; S02 will not duplicate them.

All generated neighborhoods are candidate-only. There is no 21-gate witness, global refutation, assigned-shard exhaustion, or new Lean result in this report. No repair solver has been launched by S02. Main controls all workers, leases, commits and pushes.

## Ready families and exact bindings

The scratch-root alias below means `/tmp/oec/pequalnp-pilot-18`. Every case CNF and metadata hash is recorded in its family manifest. The complete absolute-path inventory is `scratch/orch/S02/artifact-inventory.json`.

| Family | Manifest relative to scratch root | Manifest SHA-256 |
|---|---|---|
| cover-prefix controls, 14 | `cover-neighborhoods/family.json` | `d9fc444181a372b09a17a88a116a14d0316c48a77e60ef0f9e5fca667781d325` |
| cover-prefix portfolio, 144 | `cover-neighborhoods-144/family.json` | `b6463e051994e8a3bb26931a91ea1ea36bbc50361e9850a75f58a2944e869232` |
| fixed holes, 20 | `local-repairs-134218/family.json` | `585eaf7fc7e06938356e30f86a3ef562a36a3c31e2582db18bbb5efb116fed36` |
| distance K=0,2,3,4,5 | `distance-repairs-134218/family.json` | `8b9f3d4b523aad54bcea21bc35a300428fdf65fa073341015d24f7a025361e56` |

| Generator | SHA-256 |
|---|---|
| `generate_cover_neighborhoods.py` | `91bc4ce8fa0c7ce92bd6a1280cb836ca100729ced9ac1c4b7d6b66fbf97e8f68` |
| `generate_local_repairs.py` | `857f7082cb81bda879891aba76a84e59f0a1b030f6c6c0eccf08f507cf96cd97` |
| `generate_distance_repairs.py` | `39e65cae78a5bd8dd6417cf1132fb77187867d6765f20d62e10fd51bcedc9da1` |

| Review | SHA-256 |
|---|---|
| `cover-neighborhood-review.json` | `8ad5bf0d9aaf3fa4253eb3161b9713b167d59e36fe51a5f9b8b8a1a87c56e8c9` |
| `cover-neighborhood-independent-review.json` | `8a6c1a3c9b0408690faeedba7857a553d9623235038a5619ec43360c86cb5d3f` |
| `local-repair-review.json` | `23ef393d6c630c62a8980fb66c9607c6d827587f0e1e12379e931e909a22cfc8` |
| `distance-repair-review.json` | `10d172cfc013c50c9663001c4a91a844a21e621b47e91b9888deaf6070a26692` |

Both repair generators use the previously reviewed full-suffix base with size21 and first_junk=0, remove exactly its forced junk[0] unit, omit the second-junk requirement, and fix the source output selector. Prefix sorting, productivity, liveness and clean-prefix restrictions are absent. The fixed-hole family pins every other operation and fanin. The distance family uses exact keep_g equivalences for the seed operation and both canonical operands, with an exact signed totalizer bounding false keep flags. Repeated operands and virtual constants remain available.

The fixed-hole family has20 cases,3–7 holes,5045 variables and about84060–84072 clauses. Four selection modes cover output/dead-gate neighborhoods, error-influence gates, connected gate neighborhoods and uniform subsets. The distance family has K2:5118vars/84303clauses; K3:5125/84352; K4:5132/84399; K5:5136/84438. K0 is a negative encoding control, not a production search priority.

## Control status and review boundary

- Fixed-hole self-audit PASS: all20 exact clause deltas, five synthetic known22 models checked against every clause and the generic all-input validator, negative fixed-operation pin controls, and43 byte-identical reproduced files.
- Distance self-audit PASS: all five exact clause deltas,1680 keep-equivalence truth assignments,1538 signed-counter projection assignments, three synthetic known22 full-model controls, and13 byte-identical reproduced files. The K0 wrong seed has a4082-step unit-resolution contradiction replayed against the original control CNF. This proves only that the fully fixed incorrect seed cannot satisfy the target.
- Main independent source and exact-delta reviews now PASS for all20 fixed-hole and all5 distance formulas; see scratch/local-repair-independent-review.json (SHA b640a281eb3983bcad1203a9a3c71b6d277ffb3288728ffbb14d5032d408cd5f) and scratch/distance-repair-independent-review.json (SHA cf2bce81b197bd1f99f064c477de2d009b5e2fa9836b50761dfe5b53ec4c1cff). Self-audits remain explicitly separate from these main-authored independent reviews.
- Existing cover generator and controller were independently reviewed. Cover runtime statuses in NOTES are main-reported; S02 did not inspect or alter active processes.

## Seed evidence

`source-checks.json` records a fresh independent scalar evaluation of all2048 inputs for each source, including all intermediate AND values. Both circuits have20 live gates and compute exactly the target graph with one edge deleted; all their AND gates remain clean for the full target. They are useful repair seeds, not exact witnesses.

| Seed | Missing edge | Full false negatives / false positives | Source SHA-256 |
|---|---|---|
| `stochastic-candidate-134218` | (0, 9) | 18 / 0 | `3f7e31aa55a515196f4fd7f08905e0a2b08561ab09e6c93a93ae5bc6d202d813` |
| `stochastic-candidate-134219` | (1, 4) | 30 / 0 | `902ffe64e011f937c9e46372c2133c7c8fd75494d459149fc9e33ed9661f821a` |

Current families use the first seed. Its dead gate9 already computes x0 AND x9; the tail/dead seven-hole case frees gates[9,15,16,17,18,19,20]. The second seed misses edge(1,4), providing a concrete diversification option if the first pilot is inconclusive. No second-seed repair family has been generated yet.

## Initial proposed pilot (superseded by the actual launch below)

Use one repair worker initially; S06 and main own the remaining CPU allocation. Proposed caps are unbenchmarked heuristics, not predicted solve times.

| Priority | Case | Cap | Purpose |
|---|---|---|---|
| 1 | `distance-repairs-134218/distance-02.cnf` |10s|Quick small-edit probe; no fixed hole choice.|
| 2 | `distance-repairs-134218/distance-05.cnf` |30s|Allow SAT to select up to five changed descriptions.|
| 3 | `local-repairs-134218/r0004-free07.cnf` |10s|Free the missing-edge gate and output aggregation.|
| 4 | `local-repairs-134218/r0009-free07.cnf` |10s|Free distributed error-sensitive gates, including dead gate9.|
| 5 | `local-repairs-134218/r0013-free06.cnf` |10s|Change several AND branches and the output region.|
| 6 | `local-repairs-134218/r0019-free07.cnf` |10s|Randomized wider neighborhood with output and dead gate9.|

At most80 seconds of requested solver wall time in this pilot, before validation or coordination overhead. If all are inconclusive, use the second seed for a fresh distance K5 and selected six/seven-hole family before extending identical first-seed runs. K3/K4 are available but nested between K2 and K5; running every budget is not required for candidate coverage. Fixed-hole sets of size at most K are subsets of distance<=K for this numbered source; six/seven-hole cases allow changes outside the K5 region.

Any SAT model must pass the unchanged generic full-model/CNF checker and all2048-input checks, normalize to at most21 original-model gates, and receive a Lean proof. Exit20 on any local case is only an uncertified neighborhood result unless a separate certificate is checked; even certified local UNSAT proves no global or assigned-shard exhaustion.

S06 handoff: no original-DAG splitting or preprocessing work is being pursued by S02. The local families use a different full-suffix candidate encoding and must not be counted toward assigned-shard exhaustion. S08 can bind these sources, reports and manifests in the next research checkpoint review.

Sub-agents: none
TIMING total=188.4 subagents=0


## Actual launch, controller review and snapshot

Main launched one worker per family at03:27:24UTC: all20 local cases with5-second solver caps, and K2–5 distance cases with60-second caps. K0 is excluded. S02 independently reconstructed both controller sources using only their recorded literal replacements from the reviewed cover controller; all25 CNF and metadata hashes match. Verdict PASS_FOR_CANDIDATE_CONTROLLER_DELTAS, report `scratch/orch/S02/repair-controllers-review.json`, SHA `de6335c4694503cb6f4851e212ba49889c65b08af1f9b2f6d056efa61483eaac`. Local controller SHA `774a14c5c382a65b0a471f2b14530d493f9925dab19e55d323f742dcae21e360`; distance controller SHA `aaaf66c23ebd9f1415eec887e0395ba51a241b0b1bfafac93b6a04be7cf995e7`. Sources and workers were not changed.

At the bound03:28:41UTC snapshot, local completed16 uncertified UNSAT and4 UNKNOWN; the UNKNOWN cases are all four seven-hole cases r0004/r0009/r0014/r0019. Distance K2/K3 returned uncertified UNSAT, K4 UNKNOWN, K5 was incomplete at capture. Main subsequently reports K5 UNKNOWN. There is no SAT candidate and no certified local, global or assigned-shard conclusion. Exact portfolio snapshots are retained under `scratch/orch/S02/`.

## Next distinct candidate preparation

Following main direction, S02 will prepare fresh multi-source repairs with unrestricted output and topological rescheduling of the20live-gate core. Move the unused slot to early/middle/last positions, seed it with the missing edge AND, and verify that the source output remains exactly the same on all2048 inputs. Then let the distance<=K encoding choose edited descriptions and the output wire. This changes the numbered local search region while retaining the underlying near-correct function; it does not assert WLOG or exhaustive coverage. Both independently checked seeds are available. Existing sources/CNFs/workers remain unchanged, and no new search starts before main coordinates resources.

## Packaging review 2026-11-24T03:37:04.398272+00:00

`orch/S02/repairs-packaging-review.json` PASS_FOR_RESEARCH_ARTIFACT_PACKAGING, SHA `b13bea29405dfb047c3f7989b163024ac191da7ddac174a358242634a34c6747`. All17 scoped repository artifacts were inspected:14 exact direct copies and57 embedded full source files (41local,9distance,7second-stochastic). Completed totals are18 uncertified neighborhood UNSAT and6UNKNOWN; the second annealer is UNKNOWN. No credential/lease values or proof/exhaustion overclaims were found. This review does not cover unrelated repository or Lean changes.

Rescheduled generator and controls are now written under `orch/S02/`; generation/control execution is held until after the coordinated annealing wave around03:39. No additional solver, optimizer, or Lean worker was launched.

## Fresh rescheduled/free-output family ready 2026-11-24T03:41:03.153601+00:00

Prepared and self-audited after the reserved wave3 CPU window. Generator `scratch/orch/S02/generate_rescheduled_repairs.py` SHA `9276816606eb7ab1738b277bcf4c34f128b63e5158a23d54debbaadfaf88fd8c`; audit SHA `fdcee1bc8a2301a8827a6db365a32b878aee49deef35f1cf2b37ae1071649aab`. Manifest `scratch/orch/S02/rescheduled-family/family.json` SHA `5c6e8b0e103808b505b5f4977c5da9432088a67d665bbc1bb67d90b024b8b55f`; self-review `scratch/orch/S02/rescheduled-review.json` SHA `0174600253c382dd34328e4a70bff3939d2163892798fd92e1f02d412e6bd4f4`. Human-readable reproduction and scope: `scratch/orch/S02/RESCHEDULED.md`. Main independent review remains required before any coordinated launch.

There are12 source variants (two sources, original/random core order, unused slot at0/10/20) and24 distinct CNFs atK4/K5. The source output and all20live intermediate values are scalar-preserved:24576 output comparisons and491520 live-gate comparisons. Every exact CNF delta is checked against the reviewed base/output-pinned helper, deletion of exactly one output pin, and the reviewed distance gadget. All63 generated files reproduced byte-identically. Both known22 positive controls deliberately use seed outputFALSE11 but model output34, including distanceK0; full-CNF/all-input validator passes and still reports the gate limit exceeded. Restoring the removed source-output pin rejects each model. No search solver was launched.

Prioritize the genuinely different final-slot/free-output cases `s01-random-p20-k05` and `s00-random-p20-k05`, then early-slot cases `s01-original-p00-k05` and `s00-original-p00-k05`, if main elects a short pilot. These are unbenchmarked10–20second proposals, not predicted solve times. The output choice is not charged to the changed-gate budget. These families do not exhaust all21gate circuits or the assigned shard.

Sub-agents: none
TIMING total=202.3 subagents=0

## 03:48 controller checkpoint

- 2026-11-24T03:48:07.448747+00:00 — S02 rescheduled pilot controller review PASS: orch/S02/rescheduled-controller-review.json SHA585842559e599d8a87a844574ceaa89aba78efed60a3aff1a7868014237799b2. Exact8literal replacements from reviewed parent, all24CNF/metadata hashes match, exactly4K5cases selected20s/default1worker/30souterguard; lifecycle/modelvalidator unchanged. Completed03:46:55: all4UNKNOWN, noSAT/exhaustion. No workers launched/intervened. Preparing sourceanalysis and repair intake for all-positive/few-FP candidates, positiveweight16; no heavy worker authorized.

## All-positive source intake and four-case handoff

- 2026-11-24T03:54:51.471928+00:00 — S02 rescheduled10filepackaging PASS: orch/S02/rescheduled-packaging-review.json SHAeb08813e134efb7659a9704da671050f0ea05c2865bf2cab221a5031d0d2a0d5,9exactcopies+9completeembeddedfiles,4UNKNOWN/noSAT. Newpositive-repair preparation READY_MAIN_REVIEW: prepare_positive_repairs.py SHA7552f3d344d4e34a6f681b116b5ec748e032b2000315dfc9527c77f8de2bdb6b; controlreview SHA667dfab9773d414fa6603472f8678e0b0c2807c6f11f4fba5a916c4e84e3673d; handoff SHAa08d07a4e6a3b4abebe1a1a90bae0b36acabdd9fbb6ea3fd18cc6b4599d7f576. Existing savedbest3/4 from134218 ALREADY computeF_G ORx9(all2048),0FN/5boundaryFP/22fullFP, junkAND14; live21vs20. Fourfreshcases underorch/S02/positive-best3-family andpositive-best4-family: K3freeoutputdistance+5holelocaleach. ControlsPASS30720scalarchecks/840suppressionchecks/4synthetic+4realexactCNFdeltas/2fullknown22models/11reproducedfiles. Weight16 source+wrapper unchangedsupportsconfirmed; plannedcommand only,no worker launched. Recommend onlytwoK3shortpilots aftermainreview/resourcecoordination, no24case scaling. Noexact21witness/exhaustion.

See scratch `orch/S02/POSITIVE-REPAIRS.md` for exact semantics, controls and unlaunched commands. The source function has a false singleton at9, so these are known incomplete candidates. All formulas preserve the target positive AND negative boundary clauses. Local ranking only chooses editable gates; it does not relax target semantics. Output selection is free. Main review and CPU scheduling remain separate.

## Exact triangle upper-factor candidate family

- 2026-11-24T04:03:59.255084+00:00 — S02 UPPER-FACTOR CANDIDATES READY_MAIN_REVIEW: orch/S02/generate_triangle_factors.py SHAe24f9c066ab8a37fa9dbe0d028acb594b8d6d8bc83e9f482fd62e8a390920538; reviewSHA006965e4cedc6bc6264b56b52df76ae97dd5893837713a62d04766a3db13deeb; handoffSHA643c5f4025d175a4fdb759d1062c1078592ff27728199c180c1f977625cff01f. Freshtriangle-upper-factors has12permutations ofHv=F_G OR ORN(v) fortriangles(1,4,8),(3,6,7), fixedwires27/28/29. J18normalizedparent3fefefe... bodybyteunchanged; eachchild11968vars/114660clauses adds93units only. SuffixAND(27,27),AND(30,30),AND(28,31),AND(29,32) keepsallfourlive; first3junk, outputexactFG underfactororacles. ControlsPASS12288factorvalues+4096productidentities+24576suffixrows+1116units/12exactdeltas/25reproducedfiles. Sixcost-feasibleorders(4,1,8),(4,8,1),(8,1,4),(8,4,1),(6,7,3),(7,6,3); H1cost16,H3cost17. All12retained, skipinfeasibleforCPU. Exactfactorslastthreeprefix arecandidateonly, NOT WLOG orparent/globalrefutation. No fullSATmodel, solver, worker, build, lease orotheragentseedpackchange. S05ownsdirty22annealseedpack.

The full finite semantics, inherited assumptions, candidate-only scope, exactsuffix and cost table are in scratch `orch/S02/TRIANGLE-FACTORS.md`. Main independently reviews before scheduling. No claim that these three factors can simultaneously be implemented in17prefix gates is made.

## Positive controller and triangle scope follow-up

- 2026-11-24T04:07:24.400567+00:00 — S02 POSITIVE CONTROLLER PASS: run_positive_candidate_pilot.py SHAbcd50a96f66084e2c5473a348bac27ff9ce13f7fe73d33df4a2c72bb31bc7c36; orch/S02/positive-controller-review.json SHAfafffa54059b236a23939116175927ea1088bd2349226304a8ef0c2cca62015a. Exactconfig/casepathdelta only, allhelperASTsame, exactlybest3/best4K3 hashbound,20ssolver/30souter/default1worker/1GiBapproxAS, fullSATvalidator/abortlogs unchanged. No launch. TRIANGLE scopefollowup: two suffixcopies normalizeaway, so fixed17prefix familyactuallyseeks<=19effective gates(8Booleancontrols); noteSHA0b1e29ce601331c635e982dc49e009aef50454f6fd2914cac925196133fcdee3. S01newjointbound pendingmathreview would give>=18prefix for(1,4,8) and>=19for(3,6,7), henceexclude BOTH17prefixfamilies ifconfirmed. No CNF/hashchange; main/S04reviewbeforeallocatingtriangleCPU. Fresh19prefix+2AND route couldusefull21budget but NOT generated/authorizedforworker.

- 2026-11-24T04:35:46.863089+00:00 — S02 CONTEXT FAMILY READY_MAIN_REVIEW_NO_LAUNCH: six fresh exact-target/free-output neighborhoods under orch/S02/context-window-family; generator067fdd26038088ac00b5d8f4423cd7ae31efe82a1f5500744a9ce2d9eb2b5200, manifest924e77cd22bf9972b4542d31583220c8bc60621dcc4cd4c68646bf6177c01662. Nonlinear18 sourcef54738 has0FN51FP, windows[1,4,10,14,15],[2,4,10,14,15],[4,6,10,14,15,16,17,20]. Seven-FN source575c08 windows8/8/10 include dirtyAND13,outerAND15,star12,output20,ORcontext; induced connected regions verified. Independent4096scalar+2048explicitnonlinearformula checks,6base-minusjunkunit-pluspins byte comparisons,16identicalreproducedfiles PASSself. Controller7e3b17c14552b652e8789489e0c889c8fdd0c1af0db43a04a6edc7bdffcfd478 exact7configchanges fromreviewedab045,90solver/120outer/1default2maxworkers; unchangedcleanup/validator. Reviews3ee41102 and781a3a0e; fullhandoff context-window-handoff.json. No solver launched; no global/shard result. Portable earlier28CNF reconstruction alreadyPASS, sealingarchive next.

- 2026-11-24T04:39:58.278594+00:00 — S02 TWO PORTABLE ARCHIVES READY_MAIN_PRESERVATION_REVIEW: prior candidate-preservation-v1/S02-candidates.tar.gz SHAcc2a5d6751aa0f817b4a831288481da5565e9170e023e78ee769da757d404889,631915bytes/181regularmembers;150exactcopies+52embeddedfullfiles;28CNFs/68files regenerated byteexact via8generatorcommands, no rawCNFs. Preservespositive2UNKNOWN,dirty6UNSAT_UNCERTIFIED,18factorcasesretiredunrun byS04math; no global/shard/Leanresult. Newcontext-preservation-v1/S02-context.tar.gz SHAa7bfcc499d6917539c5b53cc5c7beadfe93e94853741f448e459cc548e0f4932 containsfrozencontextsources/reviews/mainPASS/launchprovenance only;6CNFs/16filesexactreproduction and2negativecontrolsPASS. Currentcontextworkeroutputs intentionallyexcludeduntilcomplete; mainlaunched andownsruntime. Allfullgenerator/auditlogs included, no creds/leasevalues/binaries. Handoff candidate-context-preservation-handoff.json SHA72ddc4abc67d916553558331444f3c3bd9bde84720b289a5ba3af68612d6b44c. No repo artifact edits/stage/push/solver/lease byS02; existingownuntracked positive-repairs andtriangle-upper-factors dirs are earlierduplicatecopies, supersededbycompactpriorarchive; leftuntouchedformainchoice.

- 2026-11-24T04:43:51.799719+00:00 — S02 NEW-SHAPE REPAIR ANALYSIS ONLY: S05triangle589 source2d99849...bfbe independentlyall2048 equalsF OR[x2(x0 ORx7)(x1 ORx4)],0FN10fullFP/6boundaryFP,all21live,junkAND6/8. Minimalextras012,024,127,247. Readonlyanalysis orch/S02/triangle589-repair-analysis/report.json SHA4aa69674efad56f1614bb6f90dd90d638f96206dfc0b304f0d9d9eb910215f60 plusfullsource/logs/offset13copy. Suggestedifmainchooses: freeoutputK3 or sevenholes[1,3,5,6,7,8,20] freeingbothdirtyANDs/ORfactors/output; broader10also14,15,16forx10-starsharing. NoCNF/feasibility/performanceclaim/worker; S05ownsseedpackandanneal. Existingcontextpilot2localUNSAT_UNCERTIFIED+3UNKNOWN,last8holecase running; preserveallwhenfinished, donotrepeat oldfiveholes.

- 2026-11-24T04:44:59.297979+00:00 — S02 CONTEXT PILOT COMPLETE: maincontrollerfinished04:43:59,2UNSAT_UNCERTIFIED(p18fiveholes) +4UNKNOWN(all8/10holes),noSAT. Full6solverstdout/stderrpairs+controllerpair+portfolio+launch+4reviews embeddedexact21files incontext-results-preservation-v1/full-results.json SHAee0a230afe1ff36700834ebfd946798df82b7530e8536b075078c00049b9912d; manifest20fc6428cbd404dcf3844148788e6a8a8ca83551c319a52077c9ae7fa1e72187; selfpackagingreview77f7a6dd00aa6b0bf9828a1985f871ccb3a637dc6fce7d4c4cdf322c0ce6ef2b. Completedhandoff S02-context-complete-handoff.json SHA5c9414baaa9cd3857483a8a6f6443b89321598aaf19c85aa46c4eb9ee827d61b bindspriorarchivecc2a5d... +contextsourcearchivea7bfcc... +fullresults+newtriangle589read-onlyanalysis. No source/CNF/controller mutation, solverlaunch, desk/gitwrite, exact21/global/shard/acceptedclaim byS02. Sub-agents: none. TIMING total=266.2 subagents=0.

- 2026-11-24T04:50:50.791757+00:00 — S02 BEST3 REPAIR FAMILY READY_MAIN_REVIEW_NO_LAUNCH: immutable134226best3 SHA9a743d5...fe96 independently2048checked F ORx2x4(x0 ORx7),0FN/fullFP21,29,85,148,149;junk17/19/all21live. Freshgeneratora32140b75f8c5d47a24cd8b05f0b25c3e9b3b0a239abdc857d5bc67f1108a598 createsconnected12holes[2,3,4,5,11,12,13,16,17,18,19,20]+freeoutputK4/K6. Originaltriangle58911holes/K4/K6 preservedseparately,NOTqueued. SixCNFbytes independentlyrebuilt(totalbothsources),4096scalars/86016intermediateevals/1344keepequivalenceassignments/300actual21countermodels+wrongthresholdcontrols/18reproducedfilesPASS. Primaryreview47a286f20100822a41d9dee9534af15d573d69c2bf29175504b325d0f04df58e. Newcontrollerd812c9cca0821e31e02cdc32b8c32307123ca406d22fa77ebd4f376adaf438b4 exact11config/logfieldchanges,unchangedlifecycle/validator,2workers120s/150outer/1000MiBeach;reviewfb0069d10d94f7fbe2590059ece5331497957b909a419171d86b62f547155732. Handoff triangle589-best3-repair-handoff.json SHA95e7a377e3f513be6fa6de225b9fa5929843b1e521c8417de5025bc2e0c20cf6. Bothone-gate+arbitraryports+freeoutputenumerations COMPLETE12362rewrites420308outputseach <0.1CPUsec,zeroexact;oldseedimproved6to5boundaryFP,newbest3noallpositiveimprovement. No solver/activeinput/lease/gitwrite. Sub-agents:none;TIMING total=272.1 subagents=0.

- 2026-11-24T04:55:02.540045+00:00 — S02 RESCHEDULED BEST3 RESERVE READY_MAIN_REVIEW_NO_LAUNCH: generator526d4ff2625b801ec283a144714484dbf70b541cee9644eac97d0b55182552c8. Twofreshcasesonly:dirty-early-h14 (old17/19junkbecome2/7;alsofreeoldaggregation14/15 beyondprevious12) andreverse-ready-k06 (junk9/14). All4096outputs+86016old/newgatevalues preserveexactsource F ORx2x4(x0 ORx7); bothfullFP21,29,85,148,149. CompleteCNFbytesrebuilt,8filesreproducedbyteexact; reviewe6007256dded7094a3cd8e17c9a35d870f23f058d68a06c7d8896cb846dca195. Controllerd53ddabc30e36fd2e210f886adf85be7bef82092c027a3097a73994c8950e4ec exact9configchanges,allfunctions/validatorunchanged,2workers180s/210outer;review7a9e147c68b099a96f09348acdff68b06ea631dc6b8d9511de70767aca085570. Handoffbest3-rescheduled-handoff.json SHAd35933f652dcad1331fc2f7b1a7caa6434202f44ffbcbfd41a2154cc26f01731. Source,CNFs,metadata,andactiveparentcontroller rehashedunchanged; newCNFhashesdisjoint. No repeatsingle-gateenum/solver/desk/gitwrite. RescheduleddomainsNOTclaimedstrictsupersetsorWLOGexhaustion. Sub-agents:none;TIMING total=276.3 subagents=0.

- 2026-11-24T05:02:24.359197+00:00 — S02 TRIANGLE/BEST3/RESCHEDULED PORTABLE PACKAGE READY_MAIN_REVIEW: triangle-repairs-preservation-v1/S02-triangle-repairs.tar.gz SHA5448d8e09646c9de7a4a025081707e599a8b032c825e9a801307c8ab1f9e313b,130000bytes/119regularmembers; manifestd2a5da77d9cf2756cbcdc430956b00e9c3c25211a2f4cc1251ecd91559f8ac2c, validation61c44858c0424e69835992d8c19bc26fadcbe7dfa8507b6a129bcafe61b99f81. All94exactcopies/8CNFs26files reproduced from12pinnedsource/seeddependencies via3generatorcommands,2negativecontrolsPASS; no solvers/enumerationsrerun. Fulloriginal3/best3three/rescheduled2sources+metadata/recipes/reviews/controllers/generationauditlogs retained. Completedbest3h12/K4/K6 allUNKNOWN120s: all3stdout/stderrpairs+controllerpair+portfolio+launch preserved. Original/rescheduledruntime explicitlyABSENT, no activeoutputsread/copied. Bothcompletedonegatecontrols12362rewrites420308outputs each/noexact retained; oldboundary5FPimprovement separately2048checkedF ORx9/22fullerrors, NOTbetterseed. Handofftriangle-repairs-preservation-handoff.json SHAd23d815703a469320000967d8a0c06854972673c921a1aae654a6a245375c06b. No rawCNF/binary/credential/leasevalue/global21/postedacceptanceclaim. Sub-agents:none;TIMING total=283.6 subagents=0.

- 2026-11-24T05:09:51.719690+00:00 — S02 NEW SCOPE COORDINATION: exact22 component-merger direction, separatefromS05 freeE sixgatecore andoldbest3rootwindows. BuildE=5+8,A=0+7+E,B=(4+5)(2+8), cleanEB and9A, remainderstars1(4+8),3(6+7),67,10(0+2+4+6). Seekglobal-OR regrouping/replacement ofcomponentpairs orlargerRgroups usingexistingnonlinearcorewires, countfullreusedcones+freshDAGnodes andvalidateexacttarget. FourCPUbusy: prepareboundedimplementation/cheapcontrols only, no solverorlongenumeration/productionadmission byS02. Frozenrepairarchive5448...unchanged.

- 2026-11-24T05:17:31.083703+00:00 — S02 OPTIONAL SHUFFLE READY_MAIN_REVIEW: source 755a6b0ac780b1d4df8241be425726657547a50e679e5afad4cf3d9d0d511d9b, diff 0bebc1eef72f2a9f2403084f09a68e400d0b281a91eafcbbe65f905c36f299e3, review 760c9d5a02e6ef5fb62ce67513c448b25e13cc873667a9ab18ca68aec05841fd; handoff orch/S02/shuffle-engine-handoff.json. FrozenS05 parent e1a686 unchanged; exact six replacements add default-off --shuffle-restarts and random Kahn all21gates before initial/fresh/best-restart mutations. All43,008,000 intermediate+2,048,000 output comparisons on1000DAGs PASS, includingdead/repeated/constants/nonlast outputs,5malformedrejections. Legacy/direct finitecontrols8exit0; default-off same snapshots/results exceptclock, enabled initialall2048 functions preserved. No production/solver/141source mutation. Main must port/review sixchanges, not replace141source; performanceunmeasured. Next S02 best4 R-first7core+finalOR repair family from immutable b6da8ac...101b0; S05owns algebra/pack. Sub-agents:none.

- 2026-11-24T05:21:22.635585+00:00 — S02 SHUFFLE WRAPPER + BEST4 CORE READY_MAIN_REVIEW: freshwrapper 99c843f9a450c37c1c283d00684015269bd2eca091da3488e8d5811b6d934944 exacttwochanges(action_store_true+conditionalargvappend), review 1c5f15d3a7f2f5a7b1d478d01d62cf58b43a4d3027804018d51e91dde3493157, handoff orch/S02/shuffle-wrapper-handoff.json. Eight finitecontrols PASS legacy/direct/default-off/enabled, abortbeforestart, forgedinexactcandidatecode10 rejectedbyunchangedrealvalidator; all lifecycle/resource/provenance pathsASTunchanged. Mainowns141integration; no duplicateintegration. Best4 generator aeda1204fd346996704d8c70052162d08daa309b67cf7606d1c04af9c8cd37e3, audit 1c1743ce501d63dfe615febf3904fe9f605c65e5677e83cea42b0cf3dd5e1e76, handoff orch/S02/best4-core-handoff.json. b6da8ac...101b0 independentlyF OR024/FP21,29,85,149; independentR13 movedbefore7core, all2048outputs43008intermediatesPASS. Coreh8 CNFc838479...c76c2/84056clauses; corestarh12 ee54d0...24de/84044, both5045vars/freeoutput/nojunkunit; exact2CNFreconstruction7filereproduction. Controller 4c1bde6e1c2712ab1eaaa9b751bbd33b926c32ce2865f9b810f949a46e70c6de exact9configchanges,1workerdefault120s/150outer/1000MiB, SATvalidatorunchanged. No production/solver/lease/gitwrite byS02. Sub-agents:none.
