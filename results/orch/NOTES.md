# L-meta-1884 orchestration notes

Only the root agent owns and renews the lease. Each strategy appends a short timestamped result here and owns a distinct scratch file under results/orch/lemmas. The final PR adds only lean/PEqualNP/Outside/L_meta_1884.lean. No credentials in notes.

Exact statement is in /tmp/oec/pequalnp-pilot-159/statement.txt; desk data in desk-001.json.

## 2026-11-25T16:41:23.841120+00:00 structural strategy

The full target is a genuine AND/OR/NOT DAG lower bound. Existing accepted reductions R_meta_1884_1, _412, _773 already occupy all three reduction slots. The cleanest existing split normalizes relabeling and the free unary input to identity inputs plus free NOT of x0; its remaining core is still the full lower bound. I wrote `results/orch/lemmas/structural.lean` with explicit singleton/edge witnesses showing every omitted nonzero vertex gives a counterexample independently of the gate budget. Awaiting restored Lean toolchain before compilation.

## 2026-11-25T16:41:25.001616+00:00 combinatorial strategy

Finite Python checks: Petersen has 15 edges, every degree is 3, no triangles, every pair has at most one common neighbour (so no 4-cycles), independence number 4, minimum vertex cover 6. The standard monotone star-cover construction costs 15+6-1=20 gates. This does not establish an arbitrary AND/OR/NOT lower bound; no valid monotone-conversion theorem has been found. Free unary x0 includes a free complement, so a proof must explicitly account for it.

## 2026-11-25T16:41:37.095208+00:00 existing_lemmas
Library route: three existing reductions for 1884. R_meta_1884_773 isolates relabeling, normalization of free unary input to !x0, and the essential lower bound on [x0,...,x9,!x0]. R_meta_1884_1 isolates ordinary Petersen >18, vertex-deleted Petersen >15, and two exceptional reader-pattern cases. R_meta_1884_412 isolates finite pivotal property and a hard circuit core. L_meta_6194 proves ≥15 non-NOT gates for ordinary Petersen. L_meta_5905 proves >14 under x0=false restriction even with !x0 free. Many 9-input lower bounds already have live-wire certificate machinery: L_meta_1938 is 7299 lines; L_meta_9818 includes all-gates 9-input target >15 and derives a 10-input 13-edge graph >16 by pinning one vertex. No existing full Petersen >18 theorem found in 50 relevant 10-input theorem headers. Headers stored in scratch library_route/ten-headers.txt.

2026-11-25T16:42:40.966876+00:00 Counterexample strategy: definitions have no apparent loophole. Standard Petersen star-cover circuit costs20 gates (15 edges, min vertex cover6). Identity10 inputs plus free NOT(x0) is the useful case. Independent-set truth table has76 false assignments. A stochastic18-gate truth-table search is running from compressed20-gate constructions; no exact witness yet. System libz3.so.4 exists and its ctypes SMT2 evaluator works; finite-certificate agent owns Kissat SAT synthesis.

## 2026-11-25T16:42:57.115943+00:00 combinatorial restriction profile

Exhaustive Python truth-table check (1024 assignments): after any one coordinate is pinned to either value, all remaining9 coordinates are essential (20/20 cases). After any two distinct coordinates are pinned, all remaining8 are essential except exactly the15 cases where both bits are true and the coordinates form an edge; these15 cases are identically true. Thus165/180 two-coordinate restrictions retain all8 variables. Three-coordinate restriction essential-count histogram:630 have7,210 have0,90 have6,30 have5. This strengthens the useful gate-elimination invariant beyond one-coordinate stability, but is not yet a circuit lower bound. Sent to structural agent.

Additional decomposition: at x0=true, f is x1 OR x4 OR x5 OR the edge function of cycle 2-3-8-6-9-7-2. At x0=false, f is the12-edge graph obtained by deleting vertex0. Sent to counterexample agent.

2026-11-25T16:43:05.190808+00:00 Root pivotal candidate independently enumerated 2640 admissible pin configurations; every configuration has a one-extra-vertex witness.

2026-11-25T16:44:34.735763+00:00 Structural draft expanded: arbitrary missing coordinate is impossible if free unary input is constant; a missing0 forces u(false)≠u(true), hence u is identity or NOT. Independent text/math review by status_review found no issue. Compilation awaits Mathlib download.

## 2026-11-25T16:44:53.991096+00:00 finite certificate strategy

Finite-certificate route: allowed Defs.LratEncoding is monotone AND/OR only, so it cannot directly encode internal NOT gates. Built official Kissat in scratch and started independent18-gate CNF/CEGAR synthesis with complete1024-row model checks. Wrote finite_certificate.lean source-clamping lemmas:≤18 gates on11 inputs normalize all sources/output to≤29, preserving semantics and gate count; pending Lean compilation. Raw search space remains enormous, so no enumeration claim is made.

2026-11-25T16:46:43.540848+00:00 SAT positive control: constructed20-gate monotone Petersen circuit (cover vertices0,1,3,7,8,9), verified1024/1024 rows; fixed CNF encoding returned SAT. Global18-gate42-row search reached UNKNOWN after120s, not evidence of UNSAT.

## 2026-11-25T16:47:15.952802+00:00 existing_lemmas
Prepared results/orch/lemmas/library_route.lean: copies the checked 15-binary-gate Petersen bound from L_meta_6194 (own BinaryBound namespace), adds a simulation of permuted/repeated inputs plus arbitrary unary free input using three NOT gates computing true, false and !x0, preserves all binary-gate counts, and concludes any target circuit of ≤18 gates has ≤3 NOT gates. Generic input relabel simulation adapted from L_meta_4934. Source ~150KB; compilation pending Defs dependencies.

## 2026-11-25T16:48:21.838860+00:00 monotone-core search

Searched final theorem statements across all current L_meta files. No full Petersen Monotone2 circuit lower bound20 found. L_meta_584/L_meta_587/L_meta_1755 provide20-gate upper bounds. L_meta_905 is a4672-line restricted AndCountCircuit≤6/read-at-most2 impossibility, not an arbitrary-monotone lower bound. L_meta_9781 is a7255-line proof that Petersen minus two adjacent edges has no monotone circuit≤16. Pure star-cover reasoning does not alone establish arbitrary monotone circuit lower bounds because nonlinear intermediate functions can filter unwanted pairs. Found L_meta_6081 already proves the two-pin pivotal property, so our independent pivotal component duplicates accepted work but can still be inlined under the import restriction.

2026-11-25T16:48:42.208619+00:00 Counterexample search update: first stochastic run48,984,677 mutations/5min, no witness; best18-gate network misses18/1024 assignments. Edge-weighted search found13-error network, still not a witness. Local exact Z3 resynthesis of random2–5 gate neighborhoods has yielded UNSAT or timeout so far; solver results are search evidence only, not Lean certificates. Root authorized ABC source build from permitted GitHub under scratch; build underway for independent AND/OR/NOT mapping experiments.

2026-11-25T16:49:42.572329+00:00 Normalization strategy: found exact accepted premises of R_meta_1884_773 in L_meta_2594 (size-preserving input relabel) and L_meta_2596 (gate-count-nonincreasing unary-to-free-NOT normalization). Inlined both under own nested namespaces into normalization.lean, with canonical_reduction discharging both premises. Only Mathlib/Defs imports; compile pending.

2026-11-25T16:50:55.957457+00:00 Normalization strategy: normalization.lean COMPILED exit 0 with no diagnostics (687 lines). Exact helpers relabel and normalize preserve/nonincrease full circuit size; canonical_reduction now derives entire posted L-meta-1884 statement from the canonical 11-wire free-NOT lower bound alone. Original checked components L_meta_2594/L_meta_2596 are inlined, no Outside imports. Root notified immediately for push-early.

2026-11-25T16:52:37.123269+00:00 Structural omission and unary-classification helpers COMPILED (exit0). Logs scratch/structural/lean.stdout and lean.stderr; two deprecation warnings only. Compiled immutable copy at scratch/structural/structural-compiled.lean.

## 2026-11-25T16:53:34.011492+00:00 checked Boolean context movement

results/orch/lemmas/combinatorial.lean compiles with Lean4.36.0, exit0, complete stdout/stderr empty at combinatorial/build-03.stdout and .stderr in scratch. It proves K(a OR b)=K(a) OR b whenever b=true forces original outputtrue, and the dual AND identity when b=false forces original outputfalse. K may contain arbitrary negation: no monotonicity assumption. A circuit transformation would replace a certifying first OR by a wire and append the same OR at output, preserving gate count; wiring/index-preservation remains to be implemented elsewhere. Exact RHS Bool operations are parenthesized.

2026-11-25T16:54:07.929892+00:00 finite source-clamping normalization COMPILED with lake env lean, exit0, clean output. File results/orch/lemmas/finite_certificate.lean. Caps29 are correct:11input+18gatewires haveindices0..28, so29remainsfalse.

2026-11-25T16:54:48.822812+00:00 Structural 132-line revision including target_separation compiled cleanly (exit0, empty stdout/stderr), SHA256 6afed0e604d5b82dd7ee18be173a3f705708b0a197d8c36c8fa988c64a45298f. Immutable copy scratch/structural/structural-002-compiled.lean.

2026-11-25T16:55:26.059702+00:00 finite-certificate output_internal compiled cleanly (interval-2 logs): for anytarget withtwoassignments agreeingatqand0 but differingtargetvalue, acomputingcircuitoutputmust beacomputedgatewire11≤output<11+size. Combinedsource nowinresults/orch/lemmas/finite_certificate.lean; sourcefrozenforrootpreservation.

## 2026-11-25T16:56:35.343539+00:00 existing_lemmas
UnaryBridge simulation compiled successfully (bridge-check-002 exit0). First full-file pass validated transplanted 3193-line binary-bound proof and found only three bridge errors, now fixed. Full recomposition compile-003 is running. Binary lower bound uses6 distinct branching wires and incidence counting; NOT costs cancel, so reweighting the existing BFS does not yield19total. Candidate refinement is excess-fanout multiplicity, especially exact15binary/3NOT case, where normalized branch incidence must be tight.

2026-11-25T16:57:04.584123+00:00 Structural generic wire-alias deletion evaluator compiled cleanly; results/orch/lemmas/structural_move.lean SHA256 be5a890e01f5d73146cb50382018fbc426103979c257f53f6a05e9655efab6d8. Full certifying-OR move construction is the next step.

## 2026-11-25T16:59:04.620618+00:00 existing_lemmas CHECKED PARTIAL
Full library_route.lean compiled with Lean exit0. `UnaryBridge.at_least_four_nots_fail` excludes every circuit with ≥4 NOT gates under the leased input format; `at_most_three_nots` proves the complementary necessary condition. Complete outputs are scratch library_route/compile-003.stdout and .stderr; warnings only. Source 3371 lines, 152620 bytes. Ready for root to merge and push.

2026-11-25T16:59:38.468103+00:00 Full certifying-OR circuit move COMPILED: results/orch/lemmas/structural_move_full.lean SHA256 79baa41391e4e762710c85ffb4e4c1f46ef4f363035380d687988c649ae78c82. Removes OR(a,b), redirects its output to a, appends OR b; same number of gates and FanInTwo, exact evaluation for fixed arity when b=true forces original outputtrue. Includes arbitrary downstream NOT/forward/default semantics.

## 2026-11-25T17:01:11.689522+00:00 finite-certificate replan

The600-second global search withatmost3NOT gates, adjacent independent-gate lex order, no deadgates, and Petersen automorphisms fixingvertex0 finished UNKNOWN on42rows (3060variables,145140clauses). This is not an UNSAT result. Source/outputnormalization is compiled and independently reviewed; a small kernel certificate for thefull search appears unlikely, so prioritize mathematical structure. A120-second phase-seeded run fromthe13-error18-gate approximation is the remaining short experiment.

2026-11-25T17:01:33.659295+00:00 ROOT REPLAN: normalization/finite-source/pivotal stages checked;≥4internalNOT case checked. Deprioritize unrestricted SAT after120s/180s/600s UNKNOWN. Continue exact3NOT tight-incidence classification, zeroNOT minterm/first-gate simplification, generic certified gate movement, and ABC/local synthesis. Full theorem still absent.

## 2026-11-25T17:02:13.481607+00:00 combinatorial component and review handoff

Compiled component: combinatorial.lean, 87 lines, SHA256 083b2d96307441768df01e1432ff9750dc7b17818ca5fac89f4737731fa749e8. build-05.stdout and build-05.stderr are empty; Lean exit0. Besides Boolean context movement, edge_tests_complete proves agreement from all true edge tests for monotone G below the target; pinned_edge_tests_complete requires only monotonicity inside one fixed-coordinate slice, and agreement on every edge with that coordinate forced false/true. For Petersen with free complementx0 this gives30 rows,27 positive. Root independently reviewed and queued the source for push.

Independent red-team reviews completed: normalization.lean (exact posted conclusion under explicit canonical lower-bound hypothesis), library_route.lean UnaryBridge/count inference, finite_certificate.lean cap29 preservation, structural_move.lean alias deletion, and structural_move_full.lean same-size certifying OR movement. Full movement SHA25679baa41391e4e762710c85ffb4e4c1f46ef4f363035380d687988c649ae78c82. No soundness issue found in reviewed source. library_route inherits three custom data declarations, which CONTRIBUTING says may require human review if eventually submitted as a full proof.

Core remains unresolved: mixed edge/highdegree intermediate functions prevent a justified reduction of arbitrary monotone circuits to star-cover formulas. Counterexample agent ran4,438,367 mutations in60seconds for a relaxed monotone18gate target on all56weight≤2 rows; no witness, best2badrows. This is negative search evidence only.

2026-11-25T17:02:49.864996+00:00 Generic move_certified compiled cleanly in structural_move_certified.lean SHA256 64ea6924cb12d6911042ba2d6b567217b781028f2b718a0366ab65927d1d9aa3. Any gate that equals earlier alias a when earlier witness b=false can be replaced by a and a final OR b, provided b=true certifies outputtrue. Same gate count and FanInTwo preserved. This extends OR(a,b) and supports AND(a,NOT b) after supplying the complementary-wire relation.

2026-11-25T17:03:09.059689+00:00 Structural limitation: the checked certifying-gate moves are only local transformations. No terminating normalization or global Petersen gate-count argument has been proved. They do not yet resolve the 18-gate lower bound, and no monotone-conversion assumption is being made.

## 2026-11-25T17:05:05.608952+00:00 existing_lemmas TIGHT CASE CHECKED
New tight_case.lean passes Lean. Exact3 internal NOT gates force size18 and15 binary gates. A least normalized ordinary Petersen circuit with binary≤15 has exactly6 branch wires; every wire occurrence count is≤2. Complete logs in scratch tight_case/compile-001.stdout/.stderr. Source frozen for root preservation. Generalization removing Least is prepared; only clean gates, no repeated binary operands, liveness and computation are needed for the branch argument.

Finite inspection of the six-step graph deletion certificate found864 winning class-deletion paths after fixing first vertex0 by symmetry, grouped into16 degree/class/isolate profiles. Every profile begins with a singleton class of residual degree3. Data/program are scratch tight_case/branch_sequences.py and profiles.txt. These profiles are exploratory, not yet a circuit obstruction.

2026-11-25T17:05:08.905000+00:00 Dead-gate removal compiled: structural_dead.lean SHA256 40c56ee92ac1adc021b2991c7c5c81c2aae13fac21cb46816fef0d953cb522c0. With positive input arity, an internal gate whose wire is neither final output nor read by any later gate can be removed, saving exactly1 gate and preserving all fixed-arity evaluations and FanInTwo. Arbitrary gate operations/forward/default semantics retained.

2026-11-25T17:05:44.545964+00:00 ABC synthesis: built current Berkeley ABC under scratch. All300 varied factoring/mapping cases were independently checked on all1024 inputs. Best normalized explicit AND/OR/NOT count20 (146 cases); no19/18-gate construction. Macro cells expanded explicitly, constants/duplicate literals normalized, one free unary input accounted for. Two bounded eSLIM runs on20-node baseline remain in progress.

## 2026-11-25T17:08:20.072299+00:00 first-OR investigation paused at root lease410

No source edits after root pause; combinatorial.lean remains the reviewed87-line compiled component. Finite safe-partner cube search is saved at scratch/combinatorial/safe_partner_cubes.txt (literal10 denotes NOT x0). For a uniquely used positive variablev other than0 entering OR(v,b), b must be independent ofv. The minimal noncertifying compatible monotone signed-input cubes have3 literals. At v1 they are {3,5,9}, {3,9,NOT0}, {4,7,8}, {7,8,NOT0}; at v2 they are {0,8,9}, {4,5,6}. Graph reasoning: on an independent assignment where b is true, every neighbour ofv that can be raised within the fixedx0 slice must already have a neighbour true; otherwise extending the independent assignment makesv pivotal while OR(v,b) remainsfixed. Petersen common-neighbour counts force those cubes.

A mixed valid partner exists already with3 gates: for source0, b=x2 AND (x1 OR (x8 AND x9)); it has a certifying edge term x1x2 and noncertifying independent triple x2x8x9. Deleting all ofb or claiming b globallycertifiesF would be invalid. Stripping its triple happens to simplify it to oneAND, so this is not a counterexample to all possible normalization.

Structural proposed a graphH of the two complementary5cycles, producing10 OR-pair outputs and using each original variable twice. This map DOES factor the Petersen function: H-distance2 pairs are Petersenedges. For every independent inputx, x_v is AND of the two incident OR outputs because its H-neighbours cannotboth be true. Any y sharing those outputs satisfies y≤x and is alsoindependent. Thus no false/true fiber collision can exclude this case. The remaining gate complexity of the quotient is the next substantive investigation, not yet performed when root paused.

## 2026-11-25T17:08:33.532696+00:00 tight finite result and pause

Compiled cleanly: results/orch/lemmas/tight_finite.lean proves Petersen ordered-pair orbits under automorphisms: equal, adjacent, and nonadjacent pairs map to (0,0), (0,1), and (0,2). This applies to ordinary10-input circuits, not to the free-complement model with0fixed. Kernel checks cover bijections, adjacency preservation, and the canonical pair images. The ordinary tight SAT encoder passed a positive control with15binary+4NOT gates and exactly6fan-outs of2. Both t0and t4 searches were interrupted after47s following the root's410 lease notice; no SAT/UNSAT conclusion. Full logs retained in scratch.

2026-11-25T17:08:35.057690+00:00
## Counterexample strategy paused after lease410

No counterexample to L-meta-1884 was found. Completed full-table stochastic runs:48,984,677 +33,453,348 +26,350,882 mutations. Best18-gate approximation had13 false positives and no false negatives. Stochastic CEGAR completed28,959,450 mutations, found a spurious30-row witness, refined to38 rows, and ended with one sample error. These are heuristic searches, not lower-bound proofs.

Local exact Z3 resynthesis tested500 random2–5 gate neighborhoods:384 UNSAT and116 timeout results; none SAT. Monotone56-row diagnostic search ran4,438,367 mutations and ended two rows short.

Berkeley ABC was built from permitted GitHub under scratch. All300 mapping experiments were verified on1024 assignments; minimum explicit normalized AND/OR/NOT cost20, reached in146 cases. Both bounded eSLIM runs (subcircuit limits6 and10) finished with20 AIG nodes and20 mapped gates unchanged. Global-limit20 eSLIM was interrupted bySIGINT on root instruction after lease410; full logs remain saved. All counterexample search processes are stopped.

Reproduction files are under /tmp/oec/pequalnp-pilot-159/counterexample/: search.py, search_weighted.py, search_anneal.py, search_cegis.py, local_smt.py, abc_explore.py, check_blif.py, macros.json, macros.genlib. Full outputs use matching .stdout/.stderr files. abc-explore-rechecked.json records all300 independently checked mappings. No Lean refutation or new compiled lemma was produced by this strategy.
