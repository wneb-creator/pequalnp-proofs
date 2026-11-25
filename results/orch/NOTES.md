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
