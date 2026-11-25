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

## 2026-11-25T03:21:17.443902+00:00 status_review: exact local search results

Exhaustive 4-variable DAG search for xy+xA+yB with zero directional traces found minimum6 gates; no witness through5 gates (13,724,932 states), first6-gate witness U=x OR B,V=y OR A,W=x OR y,T=U AND V,Z=W AND T,out=T AND Z. Exact unrestricted-OR enumeration found no2-AND implementation of any of120 C4free3x3 graphs with matching number3 (5,439,892 operand pairs). Fullplane756-critical-row mutation from66-gate seed completed228,100,000 iterations without improving66. Switched to finite_search agent65-gate seed and continuing.

2026-11-25T03:21:33.063181+00:00
## Fixed final factorization exhausted

For every one of 26 star centers and every nonempty subset S of its four incident edges (390 cases), the graph after removing S has matching number 13 when |S| is 1, 2, or 3, and matching number 12 when |S| is 4. Thus a star-built common core F followed by (F∨OR(S))∧(F∨center) costs at least 66 gates for a proper subset and 65 for a full star. C4-freeness blocks sharing a preexisting OR of two S variables from another star: every other opposite-side star meets S in at most one variable. Artifact: /tmp/oec/pequalnp-pilot-65/finite-search/fixed-factor-covers.json. This rules out the particular template, not all circuits.

## 2026-11-25T03:21:41.990142+00:00 Independent review: 65-gate construction

PASS for exact compiled 157-line core snapshot upper65-checked.lean, SHA256 4e6824bd767d81fb3436f8d667de1c28523f80fb6a792f51ad82a38205640c84. Independent parser checks all 65 gates have two distinct earlier wires. Independent symbolic minimal-monomial evaluation gives exactly the 52 incidence edges, proving full Boolean semantics computationally as a separate cross-check. Lean size, evaluation, absorption, star expansion, semantics and validity proof bodies reviewed; plain-file constraints pass. Build3 log is empty, consistent with reported exit 0. This gives a 65-gate upper construction, not a counterexample to the target bound of at most64.

The concurrently appended trace extension (230-line snapshot SHA256 391a42ec725cd3eab9ef3fc16cb006c2c52d5e7931c17590c803b75c3ee1f153) also passes mathematical inspection: both explicit singleton base arrays and recurrence traces match independent simulation, with both output traces false. Build4 is still pending, so only the 157-line core may currently be called Lean-checked.

## 2026-11-25T03:21:49.360136+00:00 mixed-cover formal lemma CHECKED

results/orch/lemmas/mixed_cover.lean compiled exit 0 with no warnings/errors. Structural proof uses Mathlib ZMod.cauchy_davenport: neighborhood of S is S+{0,12,10,4} modulo13, so a nonempty S with nonfull neighborhood has neighborhood size at least |S|+3. Hence any incidence vertex cover P,L containing neither full side has |P|+|L|≥16. Only the 169 point-line shift identities are checked by kernel decide; the 8192-subset exhaustive approach was abandoned. All helper declarations use PEqualNP.Outside.L_meta_2602_aux; imports Mathlib and PEqualNP.Defs. Full compile log /tmp/oec/pequalnp-pilot-65/toolchain/mixed-cover-build-4.log (empty). This is geometric progress only, not the full circuit theorem.

## 2026-11-25T03:22:47.824090+00:00 structure_proof — separate gate budgets

Exact exhaustive free-OR normal-form enumeration tested all circuits with at most2 AND gates on6 variables against all120 C4-free bipartite3+3 graphs with cover3. No counterexample to AND-count≥cover;4,332,705 operand cases checked in1.2s. Script/log: /tmp/oec/pequalnp-pilot-65/structure/free_or_two_and.py and free-or-two-and.log. This is computational evidence only, not a proof or Lean certificate.

Relevant existing checked results: L_meta_217 gives AND≥t for no-four-cycle graphs only t≤5, using finite classification (7353lines). L_meta_634 gives Fano AND≥7 by finite-model exclusion (4678lines). L_meta_1006 refutes a weaker boundary-only no4 cover-count assertion, with triangles; its circuit fails some positive edge-pair rows, so this is not a counterexample to the full bipartite function bound.

Strict OR≥|E| for double reread also fails without an AND budget: replace a star S=p AND N by S1=S AND N and S2=S1 AND p and reroute its uses. Both derivative directions vanish while the Boolean star remains unchanged, adding2 AND gates and no OR gates. On the plane this is66 gates with13+2 AND and51 OR. The65-gate construction found by finite_search has13 AND and52 OR. Thus either separate type count can remain optimal with double reread; excluding AND13,OR51 must be a joint optimality argument.

## 2026-11-25T03:22:54.801604+00:00 lemma_route: checked 65-gate upper witness

results/orch/lemmas/upper65.lean (230 lines, sha256391a42ec725cd3eab9ef3fc16cb006c2c52d5e7931c17590c803b75c3ee1f153) compiles with lake env lean, exit0, no warnings/errors. Full log upper65-build-4.log is empty. Exact snapshot /tmp/oec/pequalnp-pilot-65/upper65-traces-checked.lean. Defines an explicit65-gate circuit and proves its size, every gate has two distinct earlier inputs and AND/OR operation, computes full13-by13 incidence function for all26 Boolean inputs, and supplies both explicitly initialized derivative recurrence traces with zero output. All proofs use simp/norm_num/decide on finite closed data, no native_decide, bv_decide, axioms, or sorry. This is an upperbound witness at65, NOT a refutation of the posted≤64 statement.

Construction: F computes all12 line-stars except line1 (59 gates), B is OR of line1 points1,2,4,10. Output is (F OR B) AND (F OR y1), using6 more gates. Algebraically equals F OR (y1 AND B). Both factors vanish at the marked singleton inputs0 and13, forcing both formal derivativeszero.

## 2026-11-25T03:24:53.248812+00:00 Independent review: 475-line merged checkpoint

PASS for canonical SHA256 b84e02ea8843461492d9272d54c91873e51a5e7337a8b944d089fc1b9eb4fa19. Trace, mixed_cover and complete upper65 bodies are verbatim their checked source snapshots. Mixed-cover bound reviewed: Cauchy–Davenport gives neighborhood expansion by3 for a nonempty set with proper neighborhood, and complement-neighborhood containment yields cover size at least16. The 230-line upper65 trace extension now has reported build4 exit0 with empty log, confirming the previously inspected snapshot391a42. Namespace/import/options/banned-pattern checks pass. Main theorem remains absent; build005 pending at review.

## 2026-11-25T03:26:34.389121+00:00 status_review: separate-count checks and seed search

Exact free-AND C6 enumeration rules out ≤4 OR gates:113,456,790 candidate unions,584,971 closure states,20.17seconds, no timeout. Intersections are free and closed exhaustively; pruning functions false on all target edges is sound by replacing those wires by false. Full64-row equality is checked. File free_and_exact.cpp/logs in scratch. Fullplane65-seed mutation completed299,600,000 iterations with no64 witness. A6-AND free-OR Fano heuristic completed1,062,100,000 mutations with best3 mismatching rows; no witness, not a lower-bound proof.

The proposed stronger OR≥|E| from double reread is false even for single edge xy: duplicate x AND y as two distinct gates, then AND their outputs. It has3 ANDs,0 ORs, and doublezero traces. Conversely the65-plane seed retains minimum13 ANDs but uses52 ORs. Any valid joint-optimality argument must address both counts together.

2026-11-25T03:27:17.145103+00:00 upper65 existential wrapper also checked: /tmp/oec/pequalnp-pilot-65/upper65-assembly.lean,240lines, sha256973b3fa864bc62f03275afadbf732ad0d374ca18a6037f49216a522480c2df56. Build5 exit0, empty log upper65-build-5.log. Last lemma upper65_witness states the posted existential witness conditions with size upperbound65 instead of64 and outer negation removed; proves it by assembling the separately checked fields. Repository upper65 file deliberately remained230lines for reviewer/root staging; root has instruction and paths to merge wrapper afterward.

## 2026-11-25T03:27:37.548721+00:00 status_review: completed supplemental searches

C8 free-AND6-OR heuristic finished1,047,700,000 mutations without a circuit (best1 wrong critical row); 18 critical rows suffice (8 edges+10 maximal independent sets). This is inconclusive, not a proof.

All4-input quadratic graphs containing edge01 were exhaustively classified through6 total gates, using fulltruth table and both derivative bits, while allowing2 representatives per semantic signature. 853,678,469 DAG states,18.28seconds. Every graph with ordinary optimum≤6 had double-reread minimum strictly larger. Matching2 already has overhead1 (3ordinary,4double); K4 ordinary anddouble were both beyond6 and remain undetermined. Detailed per-graph table: scratch status-review/all4-log.txt.

## 2026-11-25T03:29:12.456482+00:00 structure_proof — one dirty rectangle bridge CHECKED

results/orch/lemmas/rectangle_filter.lean compiled exit0 with empty log /tmp/oec/pequalnp-pilot-65/structure/rectangle-filter-build-2.log. It proves clean point/line filter iff center is adjacent to every vertex of the opposite rectangle axis; noK22 limits such centers to one on each side when both axes have size≥2; exact Boolean-propositional absorption and expansion identities convert a rectangle filtered by centers lying inside its axes into the OR of those stars.

Concrete accounting for the combined pattern D=(OR X) AND (OR Y), output D AND (p OR l), where p∈X,l∈Y and both are clean centers: direct tree size is |X|+|Y|+1, whereas the equivalent double-star has |X|+|Y| gates. One gate is saved. If only one center is present, replacing D AND p by p AND OR Y saves the unused OR-X aggregate and one AND. These counts assume standalone linear aggregates; shared OR subnets in an arbitrary circuit remain the unresolved accounting issue.

Residual structural lemma: for a top-form circuit with exactly one dirty AND, its earlier operands are ORs of variables, and each clean top side is OR of variables with possibly that dirty gate. Clean tops cannot contain the dirty gate on both sides. Quadratic edge contributions of dirty-gate×literal filters arise only from centers belonging to its original axes, so ≤2 extra star centers cover all such contributions. Thus a star-cover extraction should cost at most (#clean tops)+2 centers, but proving a non-increasing gate-cost transformation with shared linear subnets is still needed. For multiple dirty gates, the same extraction does not yet iterate.

## 2026-11-25T03:29:42.605740+00:00 Independent review: assembled 65-gate witness and rectangle filters

PASS for upper65-assembly.lean SHA256 973b3fa864bc62f03275afadbf732ad0d374ca18a6037f49216a522480c2df56,240 lines. Prior230-line proof body unchanged; normalized statement comparison confirms the existential wrapper is exactly the posted existential with only outer negation removed and size upper64 replaced by65. Wrapper assembles the existing proved size, validity, semantics and both trace witnesses. This demonstrates the next-size case only, not a refutation.

PASS for rectangle_filter.lean SHA256 2cea172c750648c09383bf2469ba496877dd6dea62b2d827ad7553dd8c99ecba,95 lines. Seven generic lemmas reviewed: literal-filter correctness iff the selected row/column is complete, no-rectangle implies at most one complete center when opposite side has at least two vertices, and absorption/distributivity identities. Proofs correctly use one-hot assignments and elementary set/logic facts; no claim about arbitrary circuit normalization or counting. Both complete build logs are empty and root reports exit0. Plainfile/import/namespace/banned-pattern checks pass.

2026-11-25T03:31:09.348096+00:00
## Exact local resynthesis (SAT backend)

Preserved a 57-gate prefix and resynthesized the remaining eight gates using seven, with one selected line-star AND plus the final absorption construction in the window. Candidate predecessor signatures were evaluated on all 52 edge pairs, 704 maximal independent sets, and the two singleton base assignments. Equal predecessor patterns were merged, then monotone dominance retained minimal positive and maximal negative patterns plus the singleton channels; this is exact for every monotone window. One-star cases reduce to 11–12 decisive patterns. Both derivative channels are encoded exactly, with distinct ordered earlier fanins.

CaDiCaL (bundled with the Lean toolchain) proved the basic one-star windows for selected lines 0, 2, and 12 UNSAT. Line12 took 1.68 seconds; HiGHS had timed out at 240 seconds on that same instance. An eight-gate positive control was SAT in 0.05 seconds; its decoded full 65-gate circuit was independently checked on all 756 semantic test rows and both traces, with no error. Encoder: finite-search/local_sat.py; decoder/full validator: finite-search/decode_local_sat.py. Full logs: local0-sat.log, local2-sat.log, local12-sat.log, local12-control-sat.log.

Expanded predecessor sets and two/three-star windows are now running. These UNSAT results cover only the selected local windows, not arbitrary 64-gate circuits.

## 2026-11-25T03:32:41.835830+00:00 Independent review: extended rectangle filters

PASS: rectangle_filter_extended.lean,142 lines,SHA256 3ff3556daa2e53d556dbf9bd93adb4b2ebc74b6bc5269144cc5e37072568873f. Previous95-line core preserved verbatim. Three added lemmas correctly identify the pair-input footprint, force full rows/columns at centers that lie on both the filter and rectangle axes, and apply no-rectangle bounds to show at most one useful center per side. Outside-axis literals are allowed; results do not claim their disappearance on general inputs or arbitrary circuit normalization. Build1 log is empty with reported exit0; static format scan passes.

## 2026-11-25T03:38:19.369937+00:00 demasking strategy

Detailed nonformal strategy at results/orch/demasking_strategy.md. Clean g permits global F=g OR C[g:=0], with fanout(g)-1 gate savings; direct AND consumer of a clean wire can be bypassed. Universal +2 double penalty is false even for a bipartite path: g=xy, h=p OR g, a=h AND y, b=q OR a, out=h AND b computes xy OR py OR pq in5 gates (ordinary4), both marked-leaf traces false. Root bowtie optimum-double example has all ANDs clean, so bipartiteness/equality rigidity essential. Potential plane route: clean normalization to stars, size64 forces pure orientation via checked mixed-cover≥16, then first-collision tracking should preserve the point-direction trace. The notes list unresolved formal gaps and explicitly do not handle dirty ANDs. Duplicate four-input enumeration stopped after root noticed status_review already completed it.

## 2026-11-25T03:39:33.362477+00:00 Independent review: 622-line merge and two-AND trace

PASS: canonical622-line SHA256 582a330eecded7b2a20bc0b77a1f07f30efe26e915cec896cab477212b584be9. Diff147insertions/0deletions preserves prior content; approved extendedrectangle body and upper65 wrapper are unchanged. One auxnamespace and plainfile checks pass; build006 pending at review.

PASS: trace_two_and.lean,21lines,SHA256 1737675734bd7e4685f24b0a8e9b719f0a914b13d61131d48f76b5760b3c2291. Eight-Boolean identity correctly models the single-use form(D∨A)∧B withD=U∧V andOR-linear U,V,A,B; independent enumeration checks256assignments,36withpremises true. Repeated-factor implication is elementary absorption. These are restricted structural facts, not arbitrary circuit lowerbounds. Reported build1exit0, emptylog confirmed; format clean.

2026-11-25T03:40:46.465986+00:00 Refined clean strategy avoids full normalization: in a minimum all-clean-AND circuit, empty-singleton wires form a forest (one consumer, no AND consumer), forcing at least a-1 zero/mask ORs for a ANDs. Positive-support ORs of support≥2 belong to unique star centers by no-C4; union-network counts force at least |E|-a such ORs. Assigned stars cover E, so a≥τ and C≥|E|+τ−1. Equality64 gives13 distinct pure-orientation stars; first-collision trace rigidity still unproved. Full argument and remaining formal gaps recorded in demasking_strategy.md.

## 2026-11-25 03:44 UTC — structure_proof complete one-junk trace theorem

Lean-checked `results/orch/lemmas/one_junk.lean` (590 lines; SHA256 f7a32a51c951e1675f52bb22e860659e6c12d0fc7f6ba407ed7191d50725938a). Exact theorem: any valid binary AND/OR circuit computing a graph edge function, satisfying TopForm and having at most one dirty AND gate, has at least one surviving formal derivative trace at each edge. Proof uses OR-path terminal decomposition; two dirty terminals must coincide and would imply that supposedly dirty gate is below the graph function. One dirty terminal reduces to eight endpoint cases through two ANDs. Build exit 0, log `/tmp/oec/pequalnp-pilot-65/structure/one-junk-build-2.log` has only copied-helper deprecation warnings. First 405 lines reuse foundational helpers from accepted L_meta_1878; new whole-circuit theorem is original here. Root and independent reviewer notified. Remaining bridge: the actual target circuit has neither TopForm nor dirty-count bound; a normalization must preserve the double-reread witness or give strict gate savings.

## 2026-11-25T03:44:43.324487+00:00 Independent review: one dirty AND bridge

PASS: one_junk.lean, 590 lines, SHA256 f7a32a51c951e1675f52bb22e860659e6c12d0fc7f6ba407ed7191d50725938a. The copied wire/cone helper block is verbatim in L_meta_1878. New proof correctly descends from the accepted output to a clean AND, uses TopForm to classify every lower AND as dirty, and uses at most one dirty AND to eliminate deeper nesting and the same dirty factor on both sides. Remaining endpoint-path cases force one trace to survive. It applies to arbitrary simple graphs under valid AO2, exact graphFun semantics, TopForm, at most one dirty AND, and the explicit initialized trace recurrences. No size or no-rectangle hypothesis is asserted.

TopForm is essential: the posted circuit has not yet been shown to have it, and normalization can change formal derivative traces. The result must not be promoted to the original gap without those bridges. Allowed imports, nested auxiliary namespace, heartbeat option and forbidden-pattern checks pass. Complete build2 log contains eight deprecation warnings and no errors; root reports exit0.

## 2026-11-25T03:45:10.732297+00:00 status_review: exact SAT small graphs and theta lift

Independent CNF encoder small_sat.py uses one-hot ordered fanins, AND/OR semantics, and exact directional recurrences; decoded SAT models independently checked on every Boolean input. Base runs allow unused gates, so UNSAT covers every circuit of at most the budget. SAT results are computational evidence, not Lean lower-bound certificates.

- C5: ordinary≤6 UNSAT; ordinary7 SAT. Double at7 UNSAT; double8 SAT.
- C6: ordinary≤7 UNSAT; double8 UNSAT (29.79s); double9 SAT (60.74s).
- House: ordinary≤5 UNSAT; ordinary6 SAT. Double6 UNSAT for all4 edge orbits. Roof-base edge double7 UNSAT, double8 SAT.
- K4: double7 UNSAT, completing the remaining4-input sanity case.
- Bowtie (edges01,02,12,03,04,34): ordinary≤7 UNSAT (11.45s); ordinary8 SAT. Double8 on center-edge01 UNSAT; on outer triangle edge12 SAT (3.52s). Witness:5=1 AND2;6=0 OR5;7=1 OR2;8=4 OR7;9=4 OR6;10=6 AND8;11=3 OR10;12=9 AND11. Thus generic minimum-circuit no-double fails even for C4-free graphs; this example has triangles and is not bipartite. No Lean minimality claim is made.

Root then redirected effort to the bowtie bipartite double cover, theta4 (10vertices,12edges,4 length3 paths between nonincident centers). Of256 complementary two-channel routings,2 yield exact17-gate double witnesses:polarized-225.json and polarized-227.json. Inputs label paths0–6–2–5,0–7–1–5,0–8–4–5,0–9–3–5; double edges(1,7),(2,6). Direct embedding into plane markededge(0,13): inputs0..9 map to[1,0,4,5,7,17,14,13,24,18]. Full1024 rows checked;29 critical rows suffice (12edges+17 maximal independent sets).

All612 single-gate bypasses of the two seeds fail to reach16. General SAT ordinary15 and double16 timed out300s; focused AND5 double16 timed out180s, all UNKNOWN. Theta mutation from both polarizations and a17-gate absorption seed ran1,051,400,000 iterations with no16 witness. No heavy processes remain.

Shared675 exact17-gate theta variants with finite_search for plane injection:18 OR-association variants in theta-variants/ and657 mixed variants in theta-mixed-variants/. Mixed variants retain the marked nonlinear branch while replacing the other branch by all minimal-cover star assignments and OR-tree associations for its forest function. Every variant checked on all1024 rows and both zero traces. Scratch prefix:/tmp/oec/pequalnp-pilot-65/status-review/.

## 2026-11-25T03:45:24.584056+00:00 proof-resource fix CHECKED

Normalized no-rectangle proof uses translation invariance proved algebraically plus a 13^3 finite check; canonical theorem unchanged. Standalone helper results/orch/lemmas/geometry_compact.lean imports only PEqualNP.Defs. Full644-line scratch canonical at /tmp/oec/pequalnp-pilot-65/toolchain/canonical_thin.lean compiled exit0 with no warnings/errors in26.6s, peak3,924,716KiB (~3.74GiB), using CauchyDavenport + Mathlib.Tactic + Defs. With root Mathlib, even the tiny geometry file peaked7,307,496KiB; Defs-only version peaked3,039,824KiB. Full logs and machine-readable metrics retained under task scratch; metrics copied to results/orch/resource-validation.json. Root notified for independent review and canonical merge; canonical was not edited by this agent.

## 2026-11-25T03:46:13.566283+00:00 lemma_route independent review of resource fix

PASS: independent resource-fix review of canonical_thin.lean.

SHA256: 7a927bad2d530a03484c3e99d13f4c6ff9cc8bdf611bb44cd320c59d4625ebdb

644 lines. Diff only replaces full Mathlib with Mathlib.Combinatorics.Additive.CauchyDavenport + Mathlib.Tactic, keeps PEqualNP.Defs, and changes the no-rectangle proof to common-translation invariance plus a three-variable normalized finite check. Original incidence_no_rectangle statement is unchanged. Every byte from lemma incidence_point_degree through the final namespace end is unchanged.

Algebra review: subtracting l from both arguments preserves incidence offsets 0,1,3,9 in Fin13; sub_left_inj cancels the common subtraction. p≠q implies p−l≠q−l; l≠m gives m−l≠0 through symmetry. All four incidence premises transport to the normalized case with first line0 and second line m−l.

Independent exhaustive Python checks passed for translation invariance (13^3 triples), normalized no-rectangle (13^3 triples), and original no-rectangle (13^4 quadruples).

All imports allowed; only allowed scoped limit options; no forbidden patterns, quotes, attributes, axioms, or prohibited commands. No complete gap theorem exists in this partial checkpoint.

Build metrics: exit0; wall26.602342933s; maximumRSS3924716KiB (approximately3.74GiB); complete build log empty.

## 2026-11-25T03:49:20.024847+00:00 status_review: theta augmentation family exhausted

Ranked all675 verified theta17 cores against finite_search/theta_extend_virtual.py with the common39-gate8-line-star prefix and its full virtual pool of free point-pair/triple OR subexpressions. Initial single-action ranking took44.0seconds: maximum gain1; many mixed cores individually cover all8 missing edges.

The stronger source-distinction metric rejects every core. For each individually safe port-OR injection, compare its fixed source on each missing point-line pair against that line-only input. Every safe source distinguishes at most1 of the8 pairs. Exact8-bit set-cover DP therefore returns lower bound8 for all675 cores, even allowing all virtual prefix ORs optimistically without joint compatibility restrictions. Seven such port-OR injections cannot complete any core: each missing pair must acquire dependence on its outside point from some injected source. An individually unsafe OR injection cannot be repaired by further OR injections, since circuit values and derivative values are monotone in them. This is an obstruction for this augmentation family only; it does not prove the posted unrestricted circuit statement.

Complete source-cover reranking took41.2seconds. Results:/tmp/oec/pequalnp-pilot-65/status-review/theta-ranking-cover.json; per-seed records theta-rank-cover-records.jsonl; source snapshot theta-rank-source-snapshot.py; executable reproducer rank_theta_cover.py; complete log theta-ranking-cover.log. finite_search and root notified. No active process remains.

UTC 2026-11-25T03:53:16.634766+00:00
### Accepted-library search: OR budget and current upstream
- Reviewed all 64 accepted files matching OR-count/circuit-edge accounting and all 82 L_meta files added/changed in current FETCH_HEAD since initial upstream snapshot. No complete unconditional PG(2,3) size/OR bound found.
- L599/4837 proves OR >= E-1 only for induced pseudoforests; PG(2,3) fails that hypothesis. L2237/4897 needs ReadK1. L1407/2656 needs all AND gates BelowF. L4767 permits each AND to be BelowF or accept at most one graph-edge pair, yielding total E+vertexcover <= size+1; this can only help after a dirty-gate classification.
- Fresh upstream L4019 transports a dirty double-reread plane incidence to the already-normalized marked edge. L3700 eliminates a single dirty gate in an appropriately normalized least circuit. Fresh two-dirty L2264/4901 applies only to the fixed 11-vertex16-edge graph.
- L3679's counterexample has 39 inputs,64 edges,58 gates (15 AND43 OR), four nested-AND pairs. It is bipartite but NOT C4-free (selectors30,31 share data6,7); every edge has at least one nonzero directional trace. It is not a counterexample seed for our C4-free double-zero setting. Proof establishes every AND-separated realization >=59, not exact global minimum58.
- Detailed JSON census, exact fresh-upstream source snapshots, and independent L3679 computational audit are preserved under /tmp/oec/pequalnp-pilot-65 (lemma-or-count-*, new-meta-read/, lemma-3679-audit.txt).

2026-11-25T03:53:23.735693+00:00
## Theta extension and equality-case counterexample

The polarized theta4 seeds from status_review embed as an induced plane subgraph. Mapping abstract inputs 0..9 to plane inputs [3,0,12,2,8,25,16,13,20,15] sends double edge (1,7) to marked (0,13). Other eight line-stars form a 39-gate prefix. Together with theta17 and one final OR, this gives a 57-gate circuit missing exactly eight incidence edges.

Pure OR injections were exhaustively screened at every theta gate port using all fixed prefix signals and every pair/triple OR that can be prepared inside the prefix stars at no extra gate cost. Prefix OR-tree compatibility is enforced (at most two proper subsets per four-point star, nested or disjoint). Any initially unsafe OR injection remains unsafe after further OR additions, because both output values and derivative values are monotone in these additions.

For all 675 theta variants, status_review found that each initially safe source distinguishes at most one of the eight missing edge assignments from its line-only singleton. Exact set-cover lower bound is eight introduced sources, so seven OR injections cannot yield64 in this family. This is a finite obstruction for the chosen augmentation family, not a general circuit lower bound. Artifacts: finite-search/theta_extend_virtual.py and status-review/theta-ranking-cover.json.

Nevertheless, mixed theta027 plus eight injections produces a second verified 65-gate plane circuit with14 AND and51 OR gates, complementing the original13 AND/52 OR circuit. Data: finite-search/theta-extended-virtual-mixed-027.json; independent validator output theta-plane65-validation.json. All758 rows (52 positive,704 maximal negative,2 singleton) and both derivative recurrences pass.

A twelve-gate branch of this new circuit is especially informative: it computes a bipartite C4-free tree with10 edges and minimum vertex cover3, using3 AND and9 OR gates, while double-reading an edge. Thus the generic equality-case claim AND=cover andOR=edges−1 implies no double-read is false even for trees. Graph: left vertex0 adjacent to right7,8,9,10; right7 adjacent additionally to left1,2,3; right10 adjacent additionally to left4,5,6. Double edge(1,7). Formula: A=r7(l1∨l2∨l3), V=l0∨A, R=r7∨r8∨r9, B=l4∨l5∨l6; output=(B∨V)∧(r10∨V R). It simplifies to r10B∨l0(r7∨r8∨r9∨r10)∨A. All2048 rows and both traces checked. Vertex cover{0,7,10} and matching{(0,8),(1,7),(4,10)} certify cover number3. Artifact: finite-search/tree10-double12-witness.json. Ordinary circuit optimum12 has NOT yet been established; the ordinary≤11 SAT run is separate. Any global plane proof must use its special minimum-cover structure, not generic bipartite equality-case linearity.

## 2026-11-25 03:56 UTC — structure_proof active dirty gates and shared rectangle centers

Checked stronger theorem `results/orch/lemmas/one_junk_active.lean` (595 lines, Defs-only): TopForm plus at most one dirty AND active on the chosen pair forces a surviving derivative. Thus a TopForm double witness needs two distinct dirty ANDs active on its pair. Build exit0; log `structure/one-junk-active-build.log`. Reviewer notified.

Checked `results/orch/lemmas/rectangle_meet.lean` (174 lines, Defs-only): if the product of two pure bipartite rectangle functions is below the graph function, every common point is a full-row center of one rectangle and every common line is a full-column center of one rectangle. Under noK22 and all four axes having at least two elements, the unions of full centers have cardinal at most two per side and contain the entire intersection axes. This supports a shared-two-rectangle cover with at most four global centers plus one direct star center per clean top. A double accepted intersection supplies an adjacent point and line among these centers, allowing mixed-cover >=16 to force at least14AND when the cover count is <=AND+2. Still missing: actual circuit classification, singleton-axis and mixed-color dirty rectangles, and OR>=51.

Rejected stronger claim: two active dirty ANDs need not both be false on both singleton endpoints. Root supplied nontrivial forest/plane example using D1=(p or a)(p or b), D2=(q or c)(q or d), clean product and separate edge terms. Simpler redundant example x AND (x OR z), y AND (y OR w), then their AND also kills both formal derivatives with no pair-only dirty gates. Do not use the pair-only strengthening without an independent size/minimality argument.

## 2026-11-25T03:57:32.536764+00:00 Independent review: resource-safe merge and stronger structural helpers

PASS for canonical 1232-line merge, SHA256 ed3ed0416ffca92a0f50934347d4db19c2b436812b312a0feec49d4665aacc69. Previously independently reviewed canonical_thin prefix is unchanged (SHA256 7a927bad2d530a03484c3e99d13f4c6ff9cc8bdf611bb44cd320c59d4625ebdb), and the reviewed one_junk body is unchanged under equivalent nested namespace OneJunk. Build007 metrics read directly: exit0,28.70 seconds,3982708KiB peak RSS. Imports, namespace closure and forbidden-pattern checks pass.

PASS for one_junk_active.lean,595 lines,SHA256 1491416a933d6e51ae96961221ec057da9a547aeb12cc626d7753cfc9ee1077f. The assumption now bounds only dirty AND gates true on the chosen pair. All uniqueness uses correctly carry both pair-truth witnesses; the no-lower-AND argument now takes the parent truth too. TopForm remains essential.

PASS for rectangle_meet.lean,174 lines,SHA256 2543182f13e1db7f954a4f3d6e59e9551d7226675382dada1e5eb6f03a9d3bae. Shared-axis vertices must form a full row or column in one of the two clean intersected rectangles, proved by a shared-point/two-nonneighbor assignment. No-rectangle bounds then give at most two global centers on each side. Existing filter body is unchanged. Both new files use Defs-only imports, allowed namespaces, and no forbidden patterns; complete build logs have deprecation warnings only with reported exit0.
