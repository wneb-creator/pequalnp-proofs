# L-meta-2602 orchestration notes

Assigned 2026-11-25T03:07:27.169919+00:00

A step toward: Order 3 plane: no circuit of at most 64 AND/OR gates of fan-in two (distinct earlier wires) computes incidence and has a double re-read incidence (step 2 of 2)

Statement stored in /tmp/oec/pequalnp-pilot-65/statement.txt. Allowed project import: PEqualNP.Defs.

Each agent append a timestamped summary with its strategy name. Never request a desk lease; root owns renewal.

## 2026-11-25T03:09:45.997609+00:00 lemma_route

No ready full lower bound is in the permitted Defs closure. Existing checked plane bounds L_meta_1751, L_meta_2059, L_meta_4803, L_meta_5158 apply only when no AND feeds another AND; L_meta_1500, L_meta_2143, L_meta_2145 require line/point degree at most one. Three 2602 reductions still isolate nontrivial counting/structure.

Candidate generic helper file results/orch/lemmas/lemma_route.lean: activeStep; trace_carries; false_trace_no_path. These generalize the short terminal bridge of R_meta_2602_2. They are not yet compiled because toolchain setup is pending. This separates semantic trace contradiction from hard geometric path existence.

## 2026-11-25T03:09:57.080243+00:00 status_review: local counterexample search

The graph has 52 edges. Exhaustive enumeration of all 8192 choices of point-side vertices gives minimum vertex cover 13, with 2 minimizers: all points or all lines. Consequently any star-union implementation needs at least 52+13-1=64 gates, and an optimal such implementation is one of the two oriented star forms; neither has double reread. The simple duplicate-and-square modification costs +2 gates (66 total). Searching a 4-variable two-star kernel xy+xA+yB for any ≤4-gate circuit with both formal directional traces zero at xy. This is only a restricted construction search, not a proof of the posted statement.

## 2026-11-25T03:10:03.494738+00:00 structure_proof

No elementary inconsistency found. For an order-3 plane, the star circuit has 52 incidence edges + 13 star centers - 1 = 64 gates. Deleting adjacent point 0 and line 0 removes seven edges, leaving 45 edges and a diagonal matching of size 12, so the expected face lower bound is 56. A structural deletion proof would need double derivative failure to force at least nine gates absent from that face. Existing R_meta_2602_2 isolates this exact difficulty. R_meta_2602_926 already proves generic active-pair-trace collision extraction, but its four remaining hypotheses still encode the lower bound.

Existing Helpers/EdgeFnFinal gives a lower bound only for graphs with every cycle length at least 7 and no short walks between degree >=3 vertices; it cannot be applied to the projective plane (girth 6, degree 4). Generic circuit singleton/pair profiles and no-C4 normalization remain possible approaches.

## Toolchain 2026-11-25T03:10:24.555847+00:00

Initial claimed setup was absent for user agent. Installed elan 4.4.0 and pinned Lean 4.36.0 in task scratch. Source /tmp/oec/pequalnp-pilot-65/toolchain/enable.sh before Lean/checker commands. Pinned Mathlib cache-get currently running; full log in toolchain/cache-get.log. No tracked configuration changed.

## 2026-11-25T03:10:32.116219+00:00 Independent review: existing PR

PR #8105 (https://github.com/open-goat/pequalnp-proofs/pull/8105) is an open reduction R_meta_2602_493, not a complete proof. It has 92 added lines, no check runs and no comments. Its body says the collision-descent child is separately proved while two geometric children remain open. Source separates (1) derivative failure forces an AND with both inputs false on a singleton, (2) a 63–64 gate incidence circuit has an accepting pair support without a common collision, and (3) such support can avoid all collisions for one singleton. The hard size/geometric content remains in (2) and (3). Root should not count this as an existing proof; the desk's pr_open=0 appears to count proof PRs only. Full structured metadata and patch saved under /tmp/oec/pequalnp-pilot-65/review/.

2026-11-25T03:11:35.979177+00:00 lemma_route extended candidate with true_trace_reachable and trace_true_iff_reachable. New converse is by strong induction on wire index and yields full iff from arbitrary initialized recurrence trace to active-path reachability. Uses only PEqualNP.Defs. Still pending build/cache readiness.

## 2026-11-25T03:12:12.583776+00:00 Independent review: first canonical partial

Reviewed L_meta_2602.lean, SHA256 f6e8655c40762bf221fb4622a8db8a47eff98976b35880fb5d5ec674d7b02506, 55 lines. Geometry lemmas independently verified by finite Python enumeration: 52 edges, degree 4 on each side, one common line for distinct points, 45 edges after deleting marked point and line. The deleted-face cover bound follows from the twelve surviving diagonal edges and the union cardinality inequality. Namespace, imports, four-limit-option policy, plain-file rules, no banned commands/axioms/sorry/native_decide, no quotes or _root_, non-executable regular file all pass static review. No main theorem is present: this is a partial checkpoint, NOT a proof of L-meta-2602 and NOT ready for proof PR/checker acceptance. Build remains pending. Current orchestration notes accurately distinguish finite evidence and uncompiled helpers from complete proof.

2026-11-25T03:12:12.602470+00:00
## Finite-search strategy

Exact semantic-state breadth-first enumeration (truth table plus the two linearization bits) found double-reread minima: one edge on two inputs 3 gates (ordinary optimum 1); two-edge star on three inputs 4 (ordinary 2); triangle 5 (ordinary 4); C4 on four inputs 5 (ordinary 3). The three-edge path on four inputs has no witness through five gates, and standard duplication gives six (ordinary 4). Thus +2 overhead holds in these small bipartite examples but not for triangles. State search preserves two semantically equal wire copies because gate inputs must be distinct indices. Scripts and full logs: /tmp/oec/pequalnp-pilot-65/finite-search/search.py, search.log, search4.py, search4.log.

Plane finite geometry: among 8192 point subsets, only two canonical vertex covers have size 13 (entire point side or entire line side). A vertex cover containing neither full bipartition side has size at least 16. Minimum neighborhood cardinality by subset size 0..13 is [0,4,7,9,10,11,11,12,12,12,13,13,13,13]. Full computation output in finite-search/plane_cover.json. This controls star-cover circuits only; no general circuit normal form has been established.

Exact small-graph MILP synthesis started for 5-input double-star, 6 gates. Encoding checks all positive edge pairs and all maximal independent assignments (sufficient by monotonicity), plus singleton evaluations needed for the derivative channels. Timeout is only inconclusive evidence.

Toolchain 2026-11-25T03:12:45.936513+00:00: cache-get exit 0; all 9,117 pinned cache files downloaded and decompressed. Mathlib.olean present. Ready for canonical partial build after root renewal. Full log /tmp/oec/pequalnp-pilot-65/toolchain/cache-get.log.

## 2026-11-25T03:13:02.786955+00:00 structure_proof — failed local accounting routes

Exact antichain computation refutes the candidate local lemma that double reread alone forces at least nine lost face columns. Build the usual 64-gate point-star plane circuit F, then add OR(F,firstStar) and AND(F,thatOr). It still computes F, has both formal derivatives zero for every incidence pair, and deleting any incidence pair leaves exactly58 fresh gate columns. Thus only8 of66 columns disappear. Script and full log: /tmp/oec/pequalnp-pilot-65/structure/face_countercheck.py and face-countercheck.log. The size≤64/leastness/global bound must enter any valid ≥9 savings proof.

A second false candidate: double derivative failure does not force ≥3 AND gates. Let g1=xy, g2=g1 OR z, g3=g1 AND g2. This computes xy and has both derivatives zero at xy, yet uses only2 AND gates and distinct input wires. Even distinct gate functions do not suffice: g1=xy, g2=g1 OR z, g3=g1 OR w, g4=g2 AND g3 computes xy OR zw and all four gate functions differ; both derivatives at xy vanish, with2 AND gates. This circuit has an alternative3-gate implementation, so true leastness remains relevant.

Toolchain 2026-11-25T03:15:07.559017+00:00: first canonical build completed all 86 project definition modules, including PEqualNP.Defs. Target alone failed at line18 Decidable synthesis for incidence_no_rectangle. Suggested scoped synthInstance.maxSize 4096. Full build log /tmp/oec/pequalnp-pilot-65/toolchain/canonical-first-build.log. All agents can now compile scratch files against PEqualNP.Defs.

2026-11-25T03:15:56.610978+00:00 lemma_route: CANDIDATE COMPILED. results/orch/lemmas/lemma_route.lean has 127 lines. Command from lean/: source /tmp/oec/pequalnp-pilot-65/toolchain/enable.sh && lake env lean ../results/orch/lemmas/lemma_route.lean. Exit 0, no warnings/errors, full log /tmp/oec/pequalnp-pilot-65/lemma-route-build-2.log (empty). Contains activeStep, trace_carries, false_trace_no_path, true_trace_reachable, trace_true_iff_reachable, trace_unique. Generic n/C/base/source; uniqueness proves arbitrary existential recurrence witnesses agree on every valid wire. Corrected only two initially ambiguous g binders. File imports only PEqualNP.Defs and uses module_aux namespace.

## 2026-11-25T03:16:23.668804+00:00 Independent review: first compiled checkpoint

PASS: results/orch/lemmas/lemma_route.lean SHA256 a9ea2268115c54cc1a127cb591a580cf54718aa5468edbd4c76c90819ee00a97. Reviewed all 127 lines. The active-edge relation matches the derivative recurrence in both input orders; forward propagation is valid without a well-foundedness assumption, and the converse correctly uses earlier-wire validity plus the one-hot initial trace. The iff and uniqueness corollaries follow. Imports, namespace and all banned-pattern/format checks pass. Root reports lake env lean exited 0; its complete log lemma-route-build-2.log is empty, consistent with successful compilation. This is a checked partial, not the full gap theorem.

Canonical geometry file option-only update also passes: scoped synthInstance.maxSize 4096 is allowed. lean/PEqualNP/Outside/L_meta_2602.lean SHA256 bea078e0f8fafaf789b1264ed456464c6ac117f1558a91d2b53413bc9615a236. Geometry build remains pending.

## 2026-11-25T03:18:32.137518+00:00 Independent review: merged canonical checkpoint

PASS: canonical L_meta_2602.lean SHA256 778eb662e5a5dfa6248e12c68921258714858699d68715463d6afeec400e3419, 179 lines. Geometry remains as previously reviewed; trace body is verbatim the separately compiled and reviewed lemma_route body. One auxiliary namespace, allowed top imports and scoped limits, no banned patterns. This is only a merged partial checkpoint; main gap theorem remains absent. Build004 was pending at review time.

2026-11-25T03:19:31.886171+00:00
## Finite-search correction and sharp upper construction

C6 DOES have a 9-gate double-reread circuit (ordinary star circuit8), so +2 overhead is false even for bipartite C4-free graphs. Let F=y5(x0∨x4)∨y1(x0∨x2). The circuit (F∨x2∨x4)∧(F∨y3)=F∨y3(x2∨x4) repeats the edge x0-y1 in both final factors. All64 Boolean rows and both derivative traces checked directly. Full data: finite-search/cycle9-witness.json. A stochastic search found it after8,863,274 mutations; the MILP search timed out at240s without finding it. Double-star on5 inputs and4 edges, budget6, was reported infeasible by HiGHS after137.55s (not a Lean certificate).

Analogous plane circuit has65 gates, proving that any attempted bound≥66 is false. Compute F as the OR of12 line-stars excludingline1, using59 gates; then compute (F∨x1∨x2∨x4∨x10)∧(F∨y1), costing6more. Both factors vanish at singletonpoint0 and singletonline0; hence the required derivatives vanish. Exact verification used all52 edge-positive rows and all704 maximal independent negative rows (sufficient for monotone circuits), withzero mismatches. Data: finite-search/plane65-witness.json; outputwire90. The lemma_route agent is formalizing this as an upperbound partial.

Ordinary zero propagation plus dead-gate deletion at inputs0and13 leaves57gates fromthis65-gate circuit: only8 erased. Thus any unconditional claim that double-reread forces9 syntactically erased gates is false. A9-gate reduction would need Boolean restructuring, or a hypothesis size≤64.

All3770 one-gate deletions fromthe65-gate seed, replacingthatwirewithanearlierwire, were checked against all756 critical rows andthetwo derivatives. Nonegave a64-gate witness. Best candidatesmiss exactlyone positiveedge, retainingbothzeroderivatives. Data: finite-search/drop-one-results.json. status_review agent now explores multiwire mutations fromthisseed; finite_search analyzes fixedouterfactor options.
