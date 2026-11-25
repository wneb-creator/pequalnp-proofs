# pequalnp-pilot-60: L-meta-2602

Sole lease acquired 2026-11-25T02:52:22Z. Two null desk answers preceded assignment. Root owns desk and git operations.

Exact statement and assignment: /tmp/oec/pequalnp-pilot-60/assigned.json and statement.txt. Imports allowed: PEqualNP.Defs and Mathlib modules. All final helpers must use namespace PEqualNP.Outside.L_meta_2602 or _aux. Final target theorem full name top-level and last. No forbidden syntax, quotes, new axioms, sorry, native_decide or _root_.

Strategies write separate notes here and separate scratch Lean files under results/orch/lemmas; do not edit the final file. Append short findings to this file. Root will consolidate.

Toolchain: /tmp/oec/pequalnp-pilot-60/toolchain/lean-4.36.0-linux/bin. Cache setup ongoing with checker_review.

- Derivative route: candidate uniqueness and repeated-AND certificate written in `lemmas/Derivative.lean`; not yet checked pending shared definitions build. Both directional zero derivatives imply local repeated-read structures, but global 65-gate counting remains.

- Structural strategy: see structural.md. Three-active-AND shortcut is false via q=x AND y; t=q OR z; out=q AND t. Existing face≥56 and path obligations remain open; mixed dirty AND gates are the real obstacle.

- 2026-11-25T02:56:45.120860+00:00 lemma_search:2067 flat and2069 cleanAND copied into lemmas/Clean.lean; appended counterexample_shape (not yet compiled). Any target counterexample must have nestedAND and an uncleanAND gate. Face bound5985/path5987 remain open.

- Counterexample route: no index/derivative witness loophole. Small exact semantic search found matching xy OR zw has double-re-read in4 gates versus minimum3, via (xy OR z) AND (xy OR w). Thus no two-gate penalty. Plane star64 gives analogous double-re-read65. Details in counterexample.md.

- 2026-11-25T02:58:48.029919+00:00: Derivative.lean CHECKED, exit 0 under the allowed PEqualNP.Defs import. Includes derivative uniqueness, repeated-AND certificate, actual wire recurrence, and valid-output bound. Root notified immediately for partial push.

- 2026-11-25T02:59:37.255070+00:00: reduction_design: focused route is face≥56 plus double-zero restriction removes≥9 gates. Exact small search supports matching/P4 cases and disproves the analogous claim for C4, so C4-free hypothesis is essential. No fourth reduction slot. Details in reduction-design.md.

- 2026-11-25T02:59:42.487917+00:00 lemma_search: Clean.lean COMPILED exit0. counterexample_shape eliminates flat and all-cleanAND cases; remaining case must contain an uncleanAND gate. Root notified for early push.

- Structural computation: plane has704maximalindependentsets and52minimaltrueedges, so monotone specification could be checked on756patterns. Maximalindependentsets recorded in job scratch structural-max-independent.json. This is a computed observation, not yet Leanchecked.

- 2026-11-25T03:01:43.327129+00:00: Derivative path bridge CHECKED: derivative_true_iff_walk converts the posted recurrence into exact reachability through OR / singleton-guarded AND steps. Direct pair-input repeated-AND corollary is checked too. No global gate bound yet.

- 2026-11-25T03:02:14.586488+00:00: Geometry.lean CHECKED (lake env lean exit0; empty complete log geometry-build-2.log). Degree4, common-neighbor uniqueness,52edges,45faceedges,face diagonal matching12 andfacevertexcover≥12 proved without newinstances. Root notified for preservation.

- 2026-11-25T03:06:06.969090+00:00 lemma_search: Transform.lean COMPILED exit0/no warnings. Formalderivative preservation under factor substitution now proved under explicit value+derivative source domination; droppedfactor true at both target singletonseeds is sufficient. Finding suitable dirtygate remainsopen.

- 2026-11-25T03:07:16.110859+00:00: Counterexample.lean COMPILED. Concrete65gate witness satisfies exactly all posted existential conditions except upperboundchanged64to65. `tightness65` is checked by lakeenvlean. Rootnotifiedforimmediatepush.

- Structural strategy checked two new partials: FlagFragment.lean proves at most two safe line guards for two point sets each of size at least two; CanonicalFragment.lean replaces an arbitrary dirty-AND witness by a canonical false input determined by 13 point bits. Standalone Flag.lean and Canonical.lean compile, with full logs in job scratch.

2026-11-25T03:12:52.448792+00:00 Re-plan: checked partial4 includes a65-gate witness, derivative/path certificates, clean/flat exclusions, plane geometry, canonical falseinputs, a two-line flag bound, and derivative-safe substitution. Original64-gate target remains open. Generic dirtyAND-count increase is false (P4counterexample); unrestricted dirtynormalform is an existing openproblem. Active routes: complete-test heuristic64 search; global OR-count/equality analysis; firstdirtyAND structure; semantic rewiring followed by derivative-preserving dead-gate compaction. Reduction capacity is alreadyfull, so nofourthreduction willbe submitted.

- First-dirty analysis found a rigorous obstruction to factor bypass: matching xy OR zw has a 7-gate double-zero circuit whose first dirty AND has one clean mixed-OR reader, but either operand bypass introduces a nonedge. See structural.md. All 16 input rows and derivative recurrences checked computationally.

- 2026-11-25T03:19:01.553732+00:00 lemma_search: FactorElimination.lean COMPILED401lines/no warnings. Globalfunctionpreservation, proper distinctinputs undernoncollision, deadwire, unchangedderivative witnesses, zero-signature factorcriterion. CombiningwithDeadGate compactor next.

- 2026-11-25T03:21:00.116359+00:00 lemma_search: CombinedElimination.lean SOURCE ONLY prepared: conditionalactualsize dropby1 withProperdistinctinputs, samefullfunction, bothtransportedzero witnesses. Awaitingrootcomputeavailability; no newLeancheckstarted.

- CORRECTION on L_meta_1006: its6ANDgraph counterexample satisfiesonlymaximalfalseboundarytests; itdoesNOTcompute thefull edgefunction (rejects actualedge{6,7}). ItdoesnotrefutefullfunctionAND≥cover. OnlytheP4dirtyANDstrictnesscounterexampleaboveisexactfullfunction.
- ExhaustivefreeOR/≤2ANDnormalform census finished:334 C4-free3×3bipartitegraphs,1415firstANDfunctions,4465825secondANDpairs; nocircuit belowmatching/covernumber. Source and_count_small.py, JSONlog jobscratch. Thisiscomputationalevidenceonly.

- 2026-11-25T03:22:04.548672+00:00: Search64 repair and annealing completed without witness; full logs preserved in results/orch. Repair33,127,686candidates; anneal24,066,384mutations. Best64 missesoneedge, derivativeszero. Rotationsearch stillbounded/running.

- 2026-11-25T03:24:19.746215+00:00: COMPLETE DeadGate.lean CHECKED exit0; erase_eval and erase_witness preserve the full Boolean function and both posted derivative witnesses after deleting an unread nonoutput gate. Distinct earlier inputs and one-gate size decrease are checked. SHA256 0d2c7f7ca9909a3be67155a41114e289ddc1b8d198dab0ab7e3648186cc821c2.
- All bounded64searches finished without witness: repair33,127,686; rotations48,854,455 candidateevaluations; anneal24,066,384iterations. Full logs preserved; no lowerboundclaim.

- 2026-11-25T03:24:41.207105+00:00 lemma_search: CombinedElimination.lean COMPILED exit0/no warnings. Actual gate-count decrease by1, proper distinct earlier inputs, unchanged Booleanfunction, and both zero derivative witnesses now proved together under explicit local guard/zero-signature/noncollision conditions. Root notified for review/push.

- 2026-11-25T03:27:03.046601+00:00: OR-only route: no counterexample in exactAND-free searches covering allC4-freegraphs≤5vertices and all6vertexcircuits≤4ORs. General51ORplane bound remainsunproved. L724 suppliesdegree2 restrictionpayment, notdegree4. Fullalgorithm/results in or-bound-analysis.md; code or_free_and_search.cpp.

- Fooling-set AND-count investigation: exact census of all 512 bipartite 3×3 graph functions with arbitrary free OR and ≤2 ANDs found no violation (4,465,825 second-gate candidates). A separate heuristic over 2M three-AND circuits on four variables per side found no full-function counterexample; the closest pair-correct candidate has four higher-degree false positives. This remains computational evidence, not a generic proof. First-birth rectangle ownership is obstructed by later filters.

- 2026-11-25T03:28:31.888441+00:00: FirstDirty.lean CHECKED, exit 0 with empty logs. A first unclean AND always accepts a false singleton/nonedge pair; every true operand before it on a false input has an OR-only path from an active input. Full wire monotonicity is proved. FlagSemantic.lean also CHECKED: a clean fixed-line flag reader admits a safe factor. Root notified for review and preservation.

- 2026-11-25T03:29:51.418647+00:00: Thirdreduction926 fetched fromupstream andhashverified. Children6064/6066/6068/6070 splitshared/distinct repeated-AND witnesses byopposite-singletontruthvalues. It formalizesourlocalderivative route butaddsno globalcountbound. See third-reduction.md.

2026-11-25 03:42 UTC — structural: global clean extraction has exact semantic identity F=C[t:=0] OR t and preserves marked zeros for zero-signature t, but size preservation is blocked by duplicate-AND collisions after copy propagation. Idempotence cannot repair those collisions while preserving formal derivatives. See structural.md.

- COMPILED 03:38:04 UTC: `lemmas/FlagAutomorphisms.lean` proves explicit flag transitivity of the order-three incidence plane using52 tabulated automorphisms, bijectivity and all incidence preservation checked by kernel `decide`. This validates first-gate flag symmetry in the AND-count SAT search. Lean exit0; complete log `/tmp/oec/pequalnp-pilot-60/flag-automorphisms-lean.log` is empty. Parent notified immediately for review/preservation.

- derivative agent: OR-frontier strengthening fixes the earlier 7-gate absorption example, but does not by itself close global existence. A second 7-gate matching CNF circuit in `firstdirty-frontier-obstruction.json` has no frontier-safe dirty-AND factor at all, despite C4-free graph and double-zero marked derivatives. Need quantitative filtered-rectangle cost, not geometry alone.

2026-11-25 03:40 UTC reduction_design: signed width4/triple-separation plus same-side union≤6 does not force thirteen coordinates. Five words on four coordinates (a four-word implication cycle plus the all-positive width4 word) separate every subset except the four cycle words. Add eight singleton words to obtain13on12; map cycle to one plane line to satisfy all closed point rows. Full704 cross-side row constraints with this point code fixed and line widths≤4 are UNSAT, even without pair-union cuts. Details and exact computational artifacts: results/orch/signed-code-analysis.md; scripts signed_code_sat.py and plane_signed_code.py. No generic lower bound yet.

- 2026-11-25T03:40:45.338847+00:00: lemma_search: CombinedFrontier.lean CHECKED exit0, no warnings. OR-only source cone may now change on false inputs; only its first AND readers must stay below F after rewriting. Dirty source ensures output is outside cone. eliminate_factor_frontier combines this semantic theorem with zero-signature derivatives, explicit noncollision, and actual dead-gate deletion, reducing gate count by one. This handles the newer 7-gate dirty xz obstruction; the older mixed-clean-summand matching obstruction remains.

2026-11-25 03:46 UTC reduction_design: stopped signed-code search after generic26word12coordinate instance was UNKNOWN at45s. The fixed point-cycle obstruction is UNSAT even without line-width/paircuts; a three-row mathematical contradiction is recorded in signed-code-analysis.md. Reassigned to clamp compiler semantic bridge; source ready in ClampSemanticFragment.lean and standalone ClampSemantic.lean, not yet compiled during root resource hold.

- AND-count SAT outcomes: plane≤12 ANDs baseline, row-cut, and first-flag-anchored variants each ended UNKNOWN at600s; fooling5/4 ordered variant likewise UNKNOWN600s. No counterexample or UNSAT certificate for the plane. All7 CNFs, metadata, verified SHA256 hashes, and complete solver logs are preserved in `and-count-sat/`; completed scratch CNFs were removed only after lossless archive verification, reclaiming38,372,922 bytes.
- FalseRows.lean initial monolithic certificate was killed exit137; it is not claimed checked. Source is refactored into small batches with linear sortedness instead of quadratic Nodup decision and is waiting for the serial Lean slot.
- Matching extraction evidence: exact BFS requires5 gates for xy∨zw double-zero atxy when any internal nonzero t implies the target and is false onxy. All≤4 gate states exhausted;20,095 states atdepth4. Computational result only; JSON preserved in and-count-sat/.

2026-11-25 03:50:33 UTC — structural/lemma_search/derivative: implementing a proper constant-clamp compiler. Strict aliases are retained as OR padding with an unmarked input; duplicate ANDs use an earlier alias physical wire so their formal derivatives survive. This permits deletion of a gate false on every minimal positive edge, without adding a gate. Source is not yet compiled; ClampPlanFragment holds total representatives and local syntax, ClampPlanDefs the shared interface.

- derivative agent: `ClampAux.lean` checked exit0 with empty output (`clamp-aux-validation.txt`). New components: 59-line derivative-supervalue bridge, 167-line same-witness Clamp.Plan derivative transport, 86-line local Rule properness/unread/strict-alias facts. Source `alias` field renamed `strictAlias` after Lean reserved-name diagnostic. No global counterexample elimination or main gap theorem is yet claimed.

- 2026-11-25T03:54:38.647149+00:00: lemma_search: ClampValues.lean CHECKED exit0, empty log. From a local padding plan, proves representative values only shrink globally, agree wherever clamped source is false, physical base values agree when padding inputs are zero, and a positive minimal edge yields a valid non-source output representative. Actual Plan construction and assembled size-decrease wrapper remain pending.

2026-11-25 03:56:34 UTC — structural: ClampPlan.buildPlan now Lean-checked (exit0), constructing the full proper source-unread padding plan from every proper circuit and bounded distinct dummy/padding inputs. ClampPlanFragment352lines; standalone ClampPlan787lines SHA a03e38b54214db808695120a7138947ad519cd3a7404b17ebbab83532a4dc984. Semantics/derivative transport are separate checked agent results; this constructor adds no alias-existence assumptions. Frozen for root review/preservation.

2026-11-25T03:56:52.432692+00:00 reduction_design: ClampSemantic.lean passed lake env lean exit0, first check, one thread. Generic minterm preservation plus plane_semantics_from_edges and plane_clamp_semantics checked; full output clamp-semantic-check1.log. Source frozen; compiler integration handed to lemma_search. Metadata results/orch/clamp-semantic-validation.json.

- 2026-11-25T03:57:45.460839+00:00: Fresh public feed still lists L2602 open with three live reductions; sibling L2600 and children5985/5987/6064/6066/6068/6070 remain open. PR10883 and10906 for child5176 are further reductions, not proofs. No new checked count bound was found.

- 2026-11-25T03:58:39.352675+00:00: ClampComplete.lean CHECKED exit0: actual inactive_gate_smaller theorem removes any gate false on all52 minimal incidence edges, preserves the full plane function and both marked derivative zeros, keeps distinct earlier inputs, and decreases physical gate count exactly1. Padding OR aliases repairs duplicate-AND collisions without adding gates; no size63 premise or ordinary lower bound is used. The compiled source has only two inherited deprecated-if warnings. Frozen for independent review/push.

- 2026-11-25T04:00:05.525196+00:00: ClampMinimum.lean CHECKED exit0. minimum_all_active obtains a globally minimum-size proper plane realization with both marked derivatives zero from any such realization; its size is no larger and every gate accepts at least one minimal edge. This normalization explicitly allows the minimum below63 and does not assume the open ordinary lower bound. Frozen for root review/integration.

- 2026-11-25T04:11:24.891594+00:00: ClampEssential.lean CHECKED exit0 first pass. New fresh-derivative domination removes source-zero assumptions from clamping. residual_smaller deletes any gate whose canonical clamped residual retains all52 positive edges, preserving full plane semantics and both marked zeros. minimum_all_essential normalizes to a global minimum with every gate both active and essential on at least one minimal edge. No63 lower bound or unproved ordinary-minimality assumption is used. Frozen; only inherited if-name deprecation warnings.
