# L-meta-2685 orchestration notes

Assignment: 2026-11-25 02:17:00 UTC. Only root holds and renews the lease.
Exact statement: `/tmp/oec/pequalnp-pilot-58/assigned-gap.json`, gap field.
Goal: size-preserving two-level normalization of AO2 circuits for C4-free bipartite incidence functions.

Strategies:
- library route: existing accepted reductions and reusable definitions/lemmas.
- normalization route: structural transformations of mixed circuits.
- counterexample route: finite cases and semantic edge cases.
- counting route: lower bound and explicit star-cover construction.
- root: coordinate, formalize strongest route, lease/build/check/submit.

Constraints: only PEqualNP.Defs project import; target one file `lean/PEqualNP/Outside/L_meta_2685.lean`. Three reductions are already live, the posted maximum. No further reduction unless capacity is confirmed. Environment setup in progress, no Mathlib source builds.

Append dated findings below. Each agent owns its named attempt under `results/orch/lemmas/`; coordinate all changes to final file with root.
2026-11-25T02:18:54.779456+00:00
## Library route (prior_refutation_status)
- Accepted reductions R_meta_2685_1, R_meta_2685_863, R_meta_2685_41 exhaust the three slots. 863 cuts ownership budget / coverCircuitB correctness / shape. 41 cuts exact lower bound |E|+matching ≤ size+1 / star compiler, proving Konig internally.
- L_meta_4181 (1474 lines): monotone circuit → least AO2 TopForm circuit of no greater size. L_meta_4543 (1150 lines): same with Ustar minimal among least TopForm circuits.
- L_meta_1491 (2507 lines): |E|+|tops\centreless|+2|centreless|+|junk|+|orN\lam| ≤ size+|Ustar|+1; minimum vertex cover of E\Ustar ≤ |tops\centreless|.
- L_meta_3760 (10039 lines): least C4-free bipartite circuit has junk count ≠1. L_meta_1876 says zero junk implies Ustar empty. Hence missing full-normalization content starts at ≥2 junk.
- L_meta_5391 is narrow two-junk-chain surgery; L_meta_5403 proves shared-operand rigidity from no C4. These do not imply the unrestricted target.
- Only PEqualNP.Defs permitted: Outside lemmas need copied/ported within own namespace, no direct Outside imports.

2026-11-25T02:19:59.292004+00:00 counterexample route: IsAO2 has ReadsBack and exactly 2 operands; no invalid-gate loophole. Invalid output is allowed and supplies zero-cost false, so empty incidence can use empty D/P/L. SAT synthesis for C6 found 8 gates; decoded circuit independently checked on all 64 assignments. Checking 7-gate C6 and 10-gate C8 now.

2026-11-25T02:20:03.219846+00:00 LibraryRoute baseline compiled with exit 0 using only PEqualNP.Defs; 1473 lines at results/orch/lemmas/library-route.lean. Log /tmp/oec/pequalnp-pilot-58/library-route-build.log. Exported lemma PEqualNP.Outside.L_meta_2685.LibraryRoute.leastTopForm. All helpers are lemmas.
Remaining surgery coverage: 3653/4712/4741–4747 assume one junk; 3760 eliminates one junk. 5391 handles a restricted two-junk chain with unique lower reader, singleton external filters, and private removable OR ancestors. 5138 handles a prescribed two-junk 2×2-support fork with private operand wires and private edges. General sharing/branching and >=3 junk remain unproved.

2026-11-25T02:20:14.916095+00:00
## Normalization route
- A monotone AND below a linear OR must have one operand below that OR: join two assignments missing all selected inputs to contradict containment. Proof drafted as and_below_linear in normalization-route.lean, awaiting cache readiness.
- This removes ANDs for a single linear target by tracing from its output. Applied to a point cofactor, target is OR of neighbors. Main unresolved step is compatible choices across cofactors/shared gates. An OR can serve different point cofactors via conditional children, so naive unique charging fails.

2026-11-25T02:20:34.765552+00:00 counting route: existing R_meta_2685_41 uses sharp lower bound |E|+|matching|≤size+1 and star realization, with matching-cover duality already proved inside the reduction. R_meta_2685_863 uses ownership-charge, coverCircuitB semantics/size, and shape. Compiled useful partial at results/orch/lemmas/counting-route.lean: coverCircuitB_isAO2 for bounded owners/input lists, establishing backwards-read validity plus exact binary AND/OR gate shape. Exit0, full diagnostics /tmp/oec/pequalnp-pilot-58/counting-route-build.log. Next candidate is constructing the pure-side P/L witnesses for canonical cover circuits.

2026-11-25T02:21:07.507721+00:00 counterexample route: C6 exact synthesis UNSAT at7 gates in5.6s, SAT at8 with separately verified64-row truth table; path on6 vertices UNSAT at6 gates (predicted optimum7). CNF generator and complete logs scratch synth-small.py and synth-*. No counterexample found. Empty-incidence Lean branch drafted in results/orch/lemmas/counterexample-route.lean, awaiting build readiness.

2026-11-25T02:22:20.327551+00:00 counterexample route: empty_incidence exact-conclusion partial compiled via lake env lean with exit0; 21-line results/orch/lemmas/counterexample-route.lean. Log counterexample-route-build.log is empty (success). Root notified immediately for partial push.

2026-11-25T02:23:26.134369+00:00 counting route: full constructive shape component now compiled. Lemma coverCircuitB_twoLevel in results/orch/lemmas/counting-route.lean proves IsAO2 plus exactly the requested P/L pure OR closure and mixed AND operand clauses for every oppositely tagged owner list. Does not need nonempty owner lists. It discharges all of R_meta_2685_863 shaped child; hard ownership-charge budget remains. Supporting new composition argument uses closed/shaped certificates joined by P/L unions and shifting gate indices. `lake env lean` exit0, /tmp/oec/pequalnp-pilot-58/counting-shape-build.log.

2026-11-25T02:25:01.670495+00:00 LibraryRoute AO2 simplification compiled: 1149 lines / 50373 bytes, down 324 lines. Exported leastTopFormAO directly takes IsAO2. Build log /tmp/oec/pequalnp-pilot-58/library-route-build-ao.log exit0.
Multioutput route: row neighborhoods intersect pairwise in at most one. An OR-only circuit for their ORs has cost at least sum(row cardinality minus 1), since every nontrivial OR gate can lie in at most one output cone. Normalization agent has derived last-AND elimination for a joint linear family, matching Nechiporuk historical theorem. Bilinear-to-joint-row extraction remains separate: one-hot point cofactors are row-dependent copies of each original gate; no aggregate size bound follows from ordinary cofactoring. Union/intersection matrix semantics loses false multi-input/same-side assignments and is not sound for full incidence function.

2026-11-25T02:25:55.612834+00:00
## Normalization: joint linear-family elimination
Mathematical derivation: choose the last AND v in a multioutput monotone circuit whose outputs are ORs of sets A_j with pairwise intersection at most one. Its downstream paths contain only OR, hence every affected output is v OR h_j, with monotone h_j independent of v. Replace v by its linear singleton part T={a | v(1_a)=true}. This preserves every output: each target singleton is accepted by v or h_j, and monotonicity lifts each accepted singleton. If two distinct outputs are affected, T lies in both A_j and hence has at most one member; the replacement is therefore false or an input. If one output is affected, and_below_linear chooses an operand below it and bypasses v. This removes ANDs without adding gates, after standard constant/unary cleanup.
This route proves the joint row-OR theorem but does NOT yet obtain such a joint circuit from original one-output bilinear C. Reverse-mode derivative/transposition has a specific obstruction: Boolean p AND p = p, whereas ordinary product-rule derivative at p=0 vanishes. Exact cofactor propagation needs an additional Df AND Dg term. Resolving such idempotent reconvergence is part of the original difficulty.
Research lead (UNVERIFIED page claim): live search extract of Drucker thesis p34, https://people.csail.mit.edu/andyd/Drucker_PhD_thesis.pdf, attributes the joint OR-family result to Nechiporuk 1971. External page not fetched due host allowlist. No external claim is used as a formal premise.

2026-11-25T02:26:24.871264+00:00 counterexample route: complete3x3 census has15 nonempty types modulo row/column permutations and transpose;14 nontrivial one-below-bound SAT queries UNSAT; singleedge excludes zero gates directly. Complete3x4 census has39 nonempty types;37 SAT queries UNSAT, one60s UNKNOWN (C6+pendant,7edges,matching3,target8gates), plus singleedge. C8 target10 hit180s UNKNOWN. These UNSAT results are computational, not Lean-certified.
Literature filter from repository SingleLevel.lean: f_H has selector z_e adjacent to x0 and the two endpoints of e. If distinct H edges share u, their selectors share both x0 and xu, violating our no4cycle hypothesis. Therefore this family is C4-free only if H is a matching. Published counterexample applicability remains UNVERIFIED; authorized-domain search did not locate a paper copy.

2026-11-25T02:26:59.795709+00:00 elimination route: existing Helpers/ForestBound.lean claimQ proves the full |E|+cover−1 bound for forests using free OR-inputs and a good-leaf dichotomy; general C4-free graphs can have a cyclic minimum-degree-two core, where this induction does not apply. New 76-line elimination-route.lean compiles (exit0): leaf_zero, leaf_one (arbitrary-degree neighbor column deletion), duplicate_leaf_cover (sibling-leaf deletion preserves cover budget). Pure finite incidence versions avoid graph transport. No full charging bound yet.

2026-11-25T02:27:03.104230+00:00 counting route: exact constructive realization now compiled as well. coverCircuitB_size_eq proves size = sum(owner leaf lengths)+owner count−1 when all leaf lists nonempty; coverCircuitB_incidence proves exact stated incidence function for oppositely tagged owner lists covering precisely I. Together with coverCircuitB_twoLevel this discharges realization and shape children of R_meta_2685_863. Only charge (existence of owner list within C.size budget) remains. Source results/orch/lemmas/counting-route.lean; only PEqualNP.Defs import, `lake env lean` exit0, complete diagnostics /tmp/oec/pequalnp-pilot-58/counting-realize-build.log.

2026-11-25T02:27:30.962215+00:00
Normalization partial now includes shared_linear_replace: a common monotone OR operand of a family of linear outputs can be simultaneously replaced by false or a single input whenever two target supports overlap in at most one input. This is the semantic last-AND sharing replacement; Lean build completed successfully. Still needs circuit-level rewiring/cleanup, and does not extract the row circuit from original bilinear C.

2026-11-25T02:28:02.557168+00:00
## Open PR review (read-only)
- Reviewed 2026-11-25, structured `gh pr view` and fully paginated REST files; raw JSON under /tmp/oec/pequalnp-pilot-58/pr-{number}*. No PR code executed.
- https://github.com/open-goat/pequalnp-proofs/pull/5898 (head 19f0cabacfb844d602cd290c92ed6f2da9250f6d): despite title L-meta-2685, modifies existing R_meta_2685_1 into reduction with 4 hypotheses: least TopForm plus zero-junk cover bound; one-junk cover bound; >=2-junk cover bound; star compilation. No full proof. It does provide reusable incidence-to-SimpleGraph/no-C4 and cardinality bridge mathematics.
- https://github.com/open-goat/pequalnp-proofs/pull/7038: modifies same existing reduction file into size<=15 / size>15 case split; supplies no case proof.
- https://github.com/open-goat/pequalnp-proofs/pull/7705: new R_meta_2685_2 reduction assumes shared-block budget compression and budget realization. Leaves main compression burden open.
- https://github.com/open-goat/pequalnp-proofs/pull/7795: R_meta_2685_73 uses strong induction on edge sets. Terminal star bound plus a new peel hypothesis: remove nonempty star E\F, leave F nonempty and obtain D computing F with size(D)+|E\F|+1<=size(C). Hypotheses realize/shaped are already checked L_meta_3243/3245. Peel remains unproved. Author links star-forest proof in another fork; link not examined.
- None of four has comments or visible check-rollup. For5898 separately paginated REST issue comments=[], reviews=[], checkruns total_count=0. Thus no published rejection reason was found. Existing-file modifications in5898/7038 conflict with current add-exactly-one-file rule; this is our inference, not an official verdict. Three live reductions already fill posted capacity.

2026-11-25T02:29:58.506880+00:00 counterexample route: boundary-only exact encoding resolved last3x4 case (mask862) UNSAT at8 gates in70.3s using13 rows. All39 nonempty3x4 types now computationally exclude below E+matching−1.
Lean-checked generic lemma monotone_eq_of_hypergraph_boundary added to counterexample-route.lean: for finite hypergraphs, a monotone Boolean function is determined by positives on edges and negatives on maximal edge-free sets. Compilation exit0, log counterexample-route-boundary-build2.log empty. This validates reduced truth-row principle, not SAT refutation certificates. Root notified immediately.

2026-11-25T02:32:05.100678+00:00 elimination route: NEW compact support lower bound compiled, exact export EliminationRoute.essential_card_le_size: for any Circuit C with each gate reading at most two wires and S a finite set of semantically essential inputs, S.card ≤ C.size+1. No ReadsBack, AND/OR, C4-free, or graph assumptions. Proof invariant: union of supports of any finite wire set T has card ≤ processed gates + T.card; a binary gate replaces one requested wire by at most two predecessors. Helpers now combined with leaf lemmas in elimination-route.lean, compile exit0; complete log elimination-route-build.log. Counting agent is using it for the full target on all disjoint-star incidence forests.

2026-11-25T02:33:08.934884+00:00 counting route: unbounded disjoint-star support/card argument compiled. disjoint_owner_support assumes tagged nonempty owners covering I plus Nodup(flatMap(owner::leaves)), constructs essential-input set of card sum(leaf lengths)+owner count. star_forest_budget composes any valid essential-card bound with this count; instantiate with EliminationRoute.essential_card_le_size and AO2 fan-in. normal_form_of_ownership then gives exact target conclusion for all such disjoint-star forests, including arbitrary matchings. New point_essential and line_essential lemmas prove incident input sensitivity. Complete source results/orch/lemmas/counting-route.lean (Defs-only), full successful log /tmp/oec/pequalnp-pilot-58/counting-stars-build.log. General sharing charge is still unresolved.

2026-11-25T02:38:36.652577+00:00 cycle/gate-elimination route: existing MetaComplexity.L106 already proves exact size n+ceil(n/2)-1 for cycles n≥5, using L107 reader elimination (save3 at false or4 at true). NEW compiled lemmas private_neighbor, private_neighbor_sensitive, no_pair_funnel extend its semantic no-funnel argument to arbitrary triangle-free C4-free minimum-degree-two graphs; merged into elimination-route.lean, compile exit0. For maxdegree2 unions, induction with free OR inputs can close: clear free inputs for1 gate each, handle leaves as forest proof, otherwise use3/4 elimination; false deletes≤2 edges and loses≤1 cover, true creates2 free inputs while deleting≤4 edges and losing≤2 cover. Higher-degree cores still lack degree-sensitive gate savings. Porting existing full reader stack would be large; not started.
