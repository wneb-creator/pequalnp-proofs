# Pilot 178 orchestrator notes

Assigned 2026-11-25 18:58:02 UTC. Root renews every5minutes and before long runs; current expiry is recorded in scratch renew-status.json. Reductions closed.

Graph edges: 02, 13, 04, 14, 24, 05, 15, 35, 06, 26, 36, 56.

Strategies: proof_route structural NOT elimination; finite_search monotone circuit optimization / counterexample; repo_review library and certificate route; root Lean environment and synthesis. Each agent owns notes under lemmas/.

Import only PEqualNP.Defs and Mathlib. Helpers confined to target namespace. Target: lean/PEqualNP/Outside/L_meta_10760.lean.

## 19:02 UTC status

No isomorphic graph among997 analogous replacement proofs.14gate AND/OR witness is in named Lean file; reviewer independently checked128 assignments and exact desk RHS. Full theorem not yet proved. Lean4.36.0 installed into scratch; targeted Mathlib cache loading due7.84GiB filesystem. Engines:10762 packed truth-row search (certificate_search),10756 DAG verifier/library review (repo_review), direct restrictions (gate_elimination), SMT synthesis (finite_search), sampled-certificate transfer (proof_route).

##19:05 UTC

Simple gate elimination route only reaches8, theoretical restriction route ceiling11. Target has independence number2 (17false assignments). MILP found14 optimal in shared-OR biclique product class; not a general lower bound. Packed-engine Python bug (self-collisions) was independently exposed and fixed; all earlier numerical lower bounds discarded. LRAT alternative helper assembly prepared in scratch; exact LinkN2 CNF generator independently checked. No full lower bound Lean-checked yet.

##19:23 UTC re-plan

Lower13, upper14, trackedNOT extraction, and conditional final wrapper are kernelchecked and pushed. Root t1 search succeeds. Stop all SAT/alternate searches; focus on fitting the final finite certificate within memory. Split23checks initially exceeded6000MB because theorem elaboration may run concurrently. Pinned Lean source confirms proof-valued defs serialize expensive decide+kernel work while retaining synchronous auxiliary kernel checks; trying this now. Final assembly, format guard, local checker and capped cleanup follow.

## 19:50 UTC re-plan

All semantic glue is checked. Remaining issue is finite-certificate resources. Generic continuation cuts, exact keyed patches, normalized initialization, largest unary leaf(519states), and54-row unary coverage are checked and pushed. certificate_search owns the single Lean compilation slot(8GiB RAM/twoCPU), checks unary/binary leaves; repo_review owns parent coverage and restoration; proof_route plus finite_search split lower13-t0 into children. Avoid simultaneous Lean processes. Proof-valued defs serialize kernel checks; compact membership splits or bounded batches keep source below512KiB and runtime below site20minutes. Current uncommitted named file is an obsolete full split candidate; compiled olean is the checked3813-line partial. Root alone assembles final target.

## 20:10 UTC re-plan

Final scratch assembly is about508KB after helper punctuation spacing; posted theorem text remains exact. All lower13 case computations and unary leaves were checked and preserved. Main remaining work: chunked table lookups (kernel Arrays are Lists), hashed continuation coverage with full-key comparisons, complete binary groups, ordinary named-file build and checker. Both6k flat-table benchmarks exceeded6000MB; largest4061 leaf passed. Fully normalize every state field, including W.r, and k/t; use six-stage equivalent budget decoder. Drop NN-dedup route: duplicated sample pairs preserve two different contiguous segment families and cannot be removed without engine proof changes. Avoid a full scratch run followed by duplicate named build; run all leaves first in final named file after short benchmark/glue tests pass. Root owns final assembly/commits; certificate_search schedules one large Lean process.

## 20:31 UTC re-plan

All generic proof interfaces, closed root masks, and parent0 coverage have passed. Full source statement/accounting reviewed independently by gate_elimination. Initial strict forcing gave little gain; recursive normalized evaluator proved equivalent but gave no runtime gain, so do not include it in final. Two3k async lemma checks passed concurrently under4.2GiB. Same18 leaves individually took28.0s versus35.8s together. Final plan: small≤1000-cost batches in exactly two async lemma workers, largest7 leaves checked serially first, and every other expensive computational definition before the two workers. Reviewer testing one combined shallow check for all42parents; root will freeze/build full named source once final fragments ready. Whole build is first complete execution of all3199leaves; do not duplicate as a full scratch build.

## 20:39 UTC recovery: L-meta-3566

The desk withdrew10760 withHTTP410; complete frozen source and checked components are preserved in commit e4749ddb80976c66f83ad57e7ea0aa6170376ddc. Combined10760 build and localchecker were NOT run. Recovery request assigned3566; root holds only this lease, renewing every5minutes. Exactstatement in scratch gap3566/posted-statement.txt. Goal: circuit-free vertex peel for C4-free bipartite graph edgefunctions. Reductions closed.

Routes: finite_search SAT small C4-free bipartite graphs; certificate_search Boolean circuit counterexample constructions and literature; gate_elimination restriction mechanics; proof_route graph deletion/minimum cover facts; lean_setup exactAO2 upper construction; repo_review independent audit. Root composes a conditional reduction to the general edges+cover−1 lower bound while searches continue. Only one Lean process and one boundedSAT process concurrently (8GiB RAM). Newtarget lean/PEqualNP/Outside/L_meta_3566.lean; old10760 target must be excluded from any eventual newproof PR.

## 21:00 UTC re-plan:3566

Checkedandpushed: GraphPeel, exactAO2star-coverupper, conditionalpeel, Converse (postedpeel impliesfullm+cover−1), onegatezeroRestriction, Heawoodgraph/covercertificate. Named619linepartialbuildpasses; axiom auditonlypropext/Classical.choice/Quot.sound. No fullpostedprooforrefutation. FullforestboundalreadyrecordedL_meta_3525; gate_elim_two/fix_many cannotreachcyclepotential. L8933 conditionalrepairdoesnotremoveglobalsharingdifficulty.

Prioritizecounterexample: finite_search runsoneSATqueue with2GBcap and300s pergraph, startingnonplanar5×6n11m14tau5target17; certificate_search structuredshared-gateMILP onboundarytruthrows; gate_elimination preparingreversegraph/circuitmutation; lean_setup buildinggenericJSON-to-Leankernelverificationpipeline. proof_route completedsmallgraphcensuses; theseareexplicitfixedmatching/minDegree2profilecensuses whereapplicable, notallgraphs. repo_review independentlyauditsmodels/representatives. TwoCPUheavyworkersmax; coordinateRAMwithoneLeanprocess. Anycircuitbeatingm+tau−1 refutespostedstatementviacheckedConverse, so nocutlowerboundcertificateisneeded.

## 21:48 UTC re-plan:3566

The named 619-line partial still builds, but neither the posted theorem nor its negation is proved. The checked converse and conditional forward implication identify the remaining task with the unrestricted AO2 bound m + minimumCover - 1 for bipartite C4-free graphs. Graph-side certificates are checked for Heawood (14 vertices,21 edges,cover7), Graph11 (11,14,5), and a C8 extension (10,11,5). A Defs-only witness generator checks known upper circuits in seconds; no improving circuit is known. Sources, exact JSONs and complete logs are pushed under witness3566/.

Searches remain scoped evidence only. Timed SAT queries are UNKNOWN. The C8 formula/shared-helper sweep finished 137233 cost4-7 constructions without a candidate; this is not an unrestricted circuit lower bound. Reverse circuit searches, including a 260997-candidate amplification run, have found no positive gain. Safe OR helpers can be amplified by private-leaf stars; eligible AND gates can receive pendant edges. Both constructions and their compatibility/charging conditions have independent mathematical review, and saved finite controls pass full truth checks.

Current attempts: finite_search runs a C10 query with compatible safe OR-pair helpers; certificate_search probes structured sharing and the subdivision/incidence graph of K3,3 with eight compatible safe OR-triples; gate_elimination combines helper amplification with pendant cover rise. lean_setup prepares symbolic extension checking so a large amplified circuit does not require enumerating every new input assignment. proof_route revisits the missing general normalization; repo_review audits search scope and transformations. Root holds the sole3566 lease and renews every5minutes. Reassess after the current bounded trials around22:10UTC.
