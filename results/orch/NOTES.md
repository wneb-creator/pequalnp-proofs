Pilot pequalnp-pilot-180

Assigned gap: L-meta-10760. Only root holds and renews lease.

Strategies: existing proofs (proof_routes), graph isomorphism and review (status_review), SAT certificates (computational), monotone circuit search (graph_search), toolchain preparation (toolchain), root integration.

Each agent appends concise dated findings here; proof experiments go in results/orch/lemmas or job scratch. Final PR must add exactly one named Lean file; results must be removed from PR tree after durable intermediate pushes.

2026-11-25T19:10:44.428942+00:00 Computational: LRAT LinkN2 route requires copying substantial restricted imports and certificates; no SAT solver installed. Running SciPy MILP for monotone biclique cover with shared OR-subsets to find upper-bound witness. Existing L_meta_10754 SearchP provides a sound free-negation search by live-wire deletion; lower-bound adaptation remains plausible.

### 2026-11-25T19:11:19.463346+00:00 proof_routes
- Neighbor10762 has a 3797-line general-NOT search engine proving12 and giving12-gate mono witness. Neighbor10758 has6515lines and bound13. Both graph-specific sampled row matrices.
- 10754 uses free-negation binary lower bound11 plus oneNOT, mono12; six-variable core has universal vertex and is not a target deletion.
- 10712 dropOne saves one binary gate for a dependent input fixedfalse; dropTwo saves two at an unspecified value. Target no universal/leaf means special bowtie route unavailable.
- Simple biclique cover formula minimum14 gates; shared-OR cover optimization in scratch running.

2026-11-25T19:12:06.142064+00:00 graph_search: Found and exhaustively validated a 14-gate monotone witness for L-meta-10760 (output20); saved /tmp/oec/pequalnp-pilot-180/graph_search/witness14.txt and witness14.json. Restricted biclique-cover and shared-disjunction MILP optimum14. Nested formula DP over all8771 singleton/graph-edge-minterm functions also optimum14. Trying semantic DAG sharing.

2026-11-25T19:12:18.461267+00:00 sat_synthesis: official CaDiCaL source cloned; compiling. mono13 CNF generated using repository genmono.py, 21 extremal rows, 38,304 clauses, incomparable inputs and lex symmetry. Witness will be checked on all 128 inputs.

2026-11-25T19:12:54.151020+00:00 proof_routes: Constructive partial results/orch/lemmas/ProofRoutes.lean prepared,1130lines. Copies11641 signed six-variable binary bound9 and generic drop_one_var, proves target binaryCost>=10 and length>=11 when anyNOT. Exact target x6=false equals sixcore. Await root Defs build.

2026-11-25T19:14:07.841019+00:00 Computational: Computed target optimized engine at results/orch/lemmas/Computational.lean: 3744 lines,220903 bytes; regenerated501bit row blocks with189pairs (42positive groups,17negative), all numerical constants chunked below20digits. No target bound asserted yet. Existing soundness+target circuit bridge retained for compile.

2026-11-25T19:15:04.651312+00:00 graph_search: x_v=false restriction formula upper bounds by vertex0..6 are [10,10,10,10,10,10,9], so a single-variable restriction cannot provide a lower≥12. Graph automorphism group has2 elements; nontrivial map swaps0/5,1/4,2/3 and fixes6. Graph formula: (0 OR1) AND(4 OR5) OR2 AND(0 OR4) OR3 AND(1 OR5) OR6 AND(0 OR2 OR3 OR5).

2026-11-25T19:16:40.697377+00:00 sat_synthesis: CaDiCaL built. Four 300s exploratory searches: mono13/extremal21; exactly1NOT13/all128; exactly1NOT13/weight<=2; pruned exactly1NOT13/weight<=2 with onehot constraints and essential-NOT mixed input condition. Known14 pinned witness SAT; decoded and verified all128 rows, details /tmp/oec/pequalnp-pilot-180/sat_synthesis/mono14-pinned.decoded.txt. Unpinned mono14 timedout60s, no conclusion.

2026-11-25T19:16:42.596021+00:00 status_review: Independently verified witness14 on all128inputs and format-audited37line partial. No isomorphic7vertex theorem found among414candidates. Exact x6=false core occurs in11641 and14390, but only binary lower9; graph_search upper bounds all other deletions10 rule out simple one-deletion route to14. Target independence number2; maximalfalse inputs are nonedge pairs01,03,12,16,23,25,34,45,46. Any essential singleNOT must negate monotone h true on some maximalfalse pair and false on some targetedge needed byNOT; otherwise a constant replacement works. There are1977possible monotone h-signatures on allfalse inputs (excluding constanttrue). No complete structural lower13binary proof found yet.

2026-11-25T19:20:19.646138+00:00 sat_synthesis: first mono13 and exactly-one-NOT13/full128 searches timed out at300s wall (UNKNOWN). All150 local rewiring attempts around known14 witness UNSAT under pinned wiring. Launched600s exactly-one-NOT13 read-once search:30 rows (weight<=2 plus allones), essential-NOT input mixed on positive/negative pair rows, exactly one choice per gate/source, no constants/padding, one rawinput (representatives0,1,2,6) has only one operand occurrence.47,938 clauses. These pruning constraints are exploratory, not a Lean lowerbound.

2026-11-25T19:21:40.182425+00:00 Computational: full regenerated10762 soundness engine+target bridge compiled exit0 (checkpoint6354aec). Runtime-only405definition extraction avoids importingDefs; converted unsupportedX.rec toprojection code and st toits provedidentity. Runtime survey will seedrestrictioncertificate table; tinySATsurvey foundallinduced≤5types haveexactunrestrictedcost≤7.

2026-11-25T19:24:26.248417+00:00 proof_routes: ProofRoutes.lean independent math/format audit passed by status_review and toolchain. Six inherited350-digithex constants replacedwith packWords64-bit lists and independentlyverified equal. Leanvalidation running withnoerrorssofar.

### 2026-11-25T19:27:00.067417+00:00 — independent formula-search audit (toolchain agent)

Read all of `/tmp/oec/pequalnp-pilot-180/graph_search/full_formula.cpp` and its complete stdout. Source SHA256 `3a4ef9d87755dade8e7f5e2c9ae62736ff97d63c71de941fbfd5685390a49026`; stdout SHA256 `3a6cb0ec11cb620b320a194c423a9e89741035a57bca306c1b9b0f2583b025fd`. **PASS as an ordinary computed lower bound for AND/OR formulas on the 28 singleton/pair rows. This is neither Lean checked nor a circuit lower bound.**

- The seven singleton bits and 21 lexicographic pair bits represent every required test row. All 12 target edges exactly match L-meta-10760; singleton target bits are zero.
- `ix` is injective on these monotone truth vectors: any true singleton forces every incident pair true, so only pairs with both singleton endpoints false need storage. AND/OR preserve that invariant. The exact universe size is 2,350,602; uint32 arithmetic and shifts stay in range.
- Layer 0 contains all seven variables and both constants at zero cost. Each later layer enumerates every split i+j+1=c and both AND/OR; restricting to unordered splits and b<=a when i=j is complete by commutativity. Replacing a nonminimal child by a smaller formula shows that keeping only minimal-cost states loses no minimal formula. Insertion only mutates layer c, never either input layer.
- Every cumulative operation count independently recomputed from layer sizes matches stdout, ending at 7,376,368,038 operations.
- Parsed the retained checkpoint without rerunning the search: it records next cost14/partition0/index0, 2,279,002 assigned states, all14 cost histograms exactly matching layer lengths, and target index1,266,618 unassigned (255). Checkpoint SHA256 `28dc5579a4a0795c19d0230c19e5ef5faf50eefa73a042d31c2d7dfd38f2e70d`.
- Consequently any full truth-table AND/OR formula for the graph also needs at least14 binary gates, since it must agree on these28 rows. Arbitrary DAG circuits may share subexpressions, and NOT gates are absent from this search; neither case is established by this result. The44.0996-second duration is the program's own measurement, not independently timed.

2026-11-25T19:27:26.873094+00:00 proof_routes: Interruptedfirstkernelcheckafter~12minwithrootapproval; directpackWords expansion suspectedslow. Verifiedsmalltest that subtypewitness`show {n : Nat // n=packWords [...]} from ⟨_, by norm_num [packWords]; rfl⟩` elaboratestofullymaterializedNatliteral. Appliedtosixinputs,source1150lines,newvalidationrunning. Oldsource/full(empty)logs retainedscratch.

2026-11-25T19:27:32.147255+00:00 Root first re-plan (~20 minutes): no isomorphic prior theorem; all direct deletion cores too weak; formula13 excluded by independently reviewed exhaustive28-row DP (ordinary computation only). Keep14-gate witness. Prioritize seeded finite circuit certificates (91 small restrictions already kernel-checked), true/false restrictions, and single-use-input structural pruning. SAT continues to seek13-gate DAG or one-NOT witness. Stop duplicate flat-biclique/formula upper searches. Constant materialization with allowed norm_num;rfl is being tested to speed kernel evaluation while obeying numeral limits.

2026-11-25T19:28:27.367489+00:00 sat_synthesis: monotone13 critical variant has53,150 clauses, including allsampled-rowmonotonicity at every gate and operand (70covers×13gates×3values). It assumes a read-onceinput; graph_search formula14 computation justifies this for any13circuit withsharing, but this remains exploratory until Lean. SATmodels stillverified onall128rows independently.

### 2026-11-25T19:31:11.965276+00:00 — graph_search preserved-artifact checkpoint audit (toolchain agent)

GO for the twelve research files under `results/orch/graph_search/`, with their ordinary-computation labels. Preserved full_formula source and stdout exactly match the previously audited originals. Independently rechecked the14-gate witness on all128 inputs; JSON and Lean-text forms agree. Recomputed every one of the1253 table profile strings, checked unique representatives/profiles, checked capped costs against the retained DP checkpoint, and matched the complete orbit histogram. Inspected the adjacent-transposition orbit algorithm: swaps include the singleton pair and five incident-pair swaps, generate S7, and compare costs throughout each orbit. Independently validated the logged MILP selected solution as a14-gate restricted shared-disjunction biclique cover; optimality remains solver-reported. README accurately distinguishes these computations from Lean proof and circuit lower bound. Clarifications recommended: table cost14 means at least14, and MILP optimum14 is solver-reported. Full file hashes and validation output: `/tmp/oec/pequalnp-pilot-180/toolchain/graph-artifacts-audit.txt`.

2026-11-25T19:33:18.889983+00:00 graph_search: Compact formula certificate completed: 1,253 orbit representatives plus capped costs, 13,329 bytes. Independent C++ checker reconstructs 2,350,602 states and verifies 47,460,228 normalized binary inequalities in 1.24 seconds, target potential 14. This is not Lean-checked and does not establish a circuit lower bound. Preserved under results/orch/graph_search/. Root capped further formula-only formalization; switching to a full-circuit subtask.

2026-11-25T19:33:58.162647+00:00 Computational audit: compressed formula certificate checker reviewed independently; no flaw in indexing, orbit coverage, or normalized closure. Formula lower bound only, not a DAG-circuit lower bound and not yet Lean-checked. Graph_search redirected to optimizing native evaluation of generic circuit checker.

### 2026-11-25T19:36:05.671669+00:00 — independent checkpoint audit bundle (toolchain agent)

- Compressed ordinary formula certificate/checker: GO. `compressed_check.cpp` SHA256 `0e3627a7dc8a3143f5e923b2eabe0463244d51c66859eab8c1e333f575537446`; certificate `c615028f48a407efa1c3d3c24bc6cd89ba6660d53e7b5e06af7868d0e9330fae`. Coverage, orbit invariance, free-leaf values, and subadditivity on normalized pairs establish a potential lower bound for formulas. Every omitted pair has right-hand side at least14; all potentials are bounded14. No dynamic-programming checkpoint is read. README correctly labels C++/formula-only status.
- Computational engine: GO, SHA256 `c2358ddeb620ac8707c8a7e1492c302c4018fec6742ec40a4d2e1839b870a783`,3772lines. Reviewed full diff from6354aec5. Constant equality RHSs, exact target function, and full circuit bridge match previous checked text. Named sections fixed.91 distinct seed masks have checked bounds1–7; none is rootmask0. New high-bit true-restriction branch is unused by those91 seed masks. Source guard passes; supplied compile logs have76warnings and zero errors, with reported exit0.
- SingleUseBridge: GO, SHA256 `147dfdf5f5fba6a8b1fa12b72e18336d11d906addba7b679ce1b2a835cd52eb0`,197lines. New actual-Circuit.eval contradiction correctly derives output not inputi from singleton assignments, then applies absorption under the explicit condition that every rawi read uses one fixed AND/OR partner rawj. Defaults/forward references are covered by prior fold invariant. No arbitrary-circuit normalization claim. Source guard passes; owner reports compile exit0. Final integration must retain one copy of duplicated helper namespaces.
