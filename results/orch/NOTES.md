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
