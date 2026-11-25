L-meta-2592 orchestration notes

Only root calls the desk, commits, pushes, or opens a PR.
Lease obtained 2026-11-25T13:44:05.796Z; renewed at 13:45:51 UTC, expires 14:05:51 UTC.
Exact statement: /tmp/oec/pequalnp-pilot-93/statement.txt
Main proof target: lean/PEqualNP/Outside/L_meta_2592.lean
Allowed project imports: PEqualNP.Defs only. No sorry, axioms, or native_decide in results.
Append findings with strategy name and UTC time. Agents own separate scratch files under results/orch/lemmas or /tmp/oec/pequalnp-pilot-93. Never edit another agent file.
Reductions open, but desk reports reductions_live=3 (capacity full).

2026-11-25T13:48:22.280644+00:00 counterexample_search: Petersen truth table has 76 false inputs and 5 maximum independent sets of size 4. C++ full-truth-table CGP search is running from 20-gate cover constructions, deleting one gate and allowing AND/OR/NOT mutations; no exact 19-gate witness so far. Source and complete log in /tmp/oec/pequalnp-pilot-93/search_cgp.cpp and search_cgp.log.

Structural strategy, timestamp corrected at 2026-11-25T13:50:40 UTC: Found checked L_meta_4725 (146284 bytes / 3224 lines), exact binary floor 15 + notCount C <= C.size for Petersen edge function. Proof uses six necessary branch wires plus input count. This rules out >=5 NOT gates at budget19; 1–4 NOT remain. Extracted namespace-renamed partial to results/orch/lemmas/Structural.lean, awaiting Lean toolchain. finite_certificate owns first-gate dependency map; reduction_routes owns fewNot R4727 map.

Root 13:48 UTC: Lean v4.36.0 installed locally under /tmp/oec/pequalnp-pilot-93/elan. Use PATH=/tmp/oec/pequalnp-pilot-93/elan/bin:$PATH ELAN_HOME=/tmp/oec/pequalnp-pilot-93/elan. Mathlib cache get in progress; wait for root before builds.

2026-11-25T13:49:24.868282+00:00 reduction_routes: examined all R2592 and R4727 cuts. R4727_17 compile completed L6060 but lower bound L6062 still conjecture; R4727_53 signed compile completed L7227 but signedBound L7229 still conjecture. No closed assembly via either route. Wrote generic last-NOT factorization candidate results/orch/lemmas/Reduction.lean, awaiting cache for Lean validation.

2026-11-25T13:49:42.361116+00:00 finite_certificate: R651_1 first-gate branches L1884/L1886/L1888/L1890 remain unproved. Nonedge-OR normalized cases L5236 (3–4 NOT) and L5238 (>=5 NOT) are checked, but L5234 (1–2 NOT) and L5232 (monotone) remain open. Found Lean-bundled cadical; generated 30-row weak circuit CNF (15 minimal true + 15 maximal false), 139710 clauses, waiting root renewal before search.

2026-11-25T13:50:40.738267+00:00 structural: Added largeNotImpossible for >=5 NOT; file 146975 bytes, 3239 lines. Format string scans no forbidden root identifier, quotes, sorry, axiom, or native_decide. Binary floor core proves six needed first-branch groups and counts 10 inputs+6 branch slots−1=15 binary gates. Strengthening requires additional graph-sensitive branching beyond vertex-cover/twin-group argument.

2026-11-25T13:52:09.146498+00:00 counterexample_search: Unconstrained 19-gate search reached exactly 5 false-positive rows by computing Petersen plus nonedge {5,6}; no witness. Forced-output-reachable-NOT search reached 15 errors. Independently generated and exhaustively checked an exact 20-gate monotone circuit on all 1024 rows, stored in /tmp/oec/pequalnp-pilot-93/petersen_upper20.json. Search heuristic is not exhaustive and proves no lower bound.

2026-11-25T13:53:03.491248+00:00 reduction_routes: results/orch/lemmas/Reduction.lean compiled with sole import PEqualNP.Defs, exit 0 and empty compiler output. 98 lines frozen for checkpoint. Proves generic last-NOT cut exactly (the first hypothesis of R2592_318), preserving all gates and semantics even for empty/invalid NOT operands. Full log /tmp/oec/pequalnp-pilot-93/reduction-final-build.txt.

2026-11-25T13:56:20.400635+00:00 finite_certificate: Finite.lean passes lake env lean (coverage2 stdout/stderr empty, exit0). Kernel-checked76 false rows; selected30 rows distinct/bounded; coverage gives finite_rows_complete for any inclusion-monotone Boolean function. SAT30-row exactly1NOT solved SAT33s but was an antitone separator, wrong on many untested rows. All-types30-row SAT likewise spurious. Exactly1NOT92-row (all76false+15edges+1023) search running300s cap; full1024 exactly3NOT CNF prepared with1,433,488clauses (32.1MB) for nextrenewal.

2026-11-25T13:56:28.426066+00:00 structural: Structural.lean compiled successfully (exit0), full warnings-only log /tmp/oec/pequalnp-pilot-93/structural-build.log. Structural16.lean wraps existing L5236 signed certificate to get global16binary floor and exclude>=4NOT; global16floor is also already checked as L6581. Compiling Structural16 with scratcholean. Retention.lean builds finite400case certificate that the first binary gate must retain one input operand; reduction_routes handles restriction charging2 and automorphisms toward17binary floor.

2026-11-25T13:57:35.249249+00:00 counterexample_search: 19-gate monotone near-candidate improved to 4 errors, exclusively maximal independent triples {1,3,7}, {0,7,8}, {0,3,9}, {1,8,9}. This is a monotone overapproximation, NOT a counterexample. Candidate is latest BEST 4 in search_cgp.log. Exhaustive two-gate rewrite windows inserting a NOT are running; no witness.

2026-11-25T14:03:07.617393+00:00 structural: RetentionStandalone.lean (71312bytes) compiled exit0; companion Retention.lean alsoexit0. New first_both_retained proves both firstbinaryoperands staylive, using400finite witnesscases checked by kernel. Circuit extraction realizes original10pins. Root notified forindependentreview+push. Structural16fullsignedcertificate remainscompiling withoutreportederrors.

2026-11-25T14:05:47.740611+00:00 counterexample_search: All 21 restricted SAT repair windows were UNSAT on all1024 input rows (not an unrestricted lower bound). Exhausted 1,393,536 single-consumer rewrites after inserting oneNOT into the18-gate near-circuit, and 8,275,134 two-consumer beam rewrites: no improvement below4errors. Forced-active-NOT CGP finished600seconds /1,483,600,000 mutations, best8errors. Complete computational report and source hashes: /tmp/oec/pequalnp-pilot-93/counterexample-search-report.json. Unconstrained20minute CGP stillrunning.

2026-11-25T14:06:06.101523+00:00 structural: Full Structural16.lean compiled successfully (exit0), wrappers provide 16 + notCount C <= size and exclude >=4 NOT. Full source285634bytes; log /tmp/oec/pequalnp-pilot-93/structural16-build.log. Retention companion recompiled against full Structural16.olean; independent review underway. New floor17 proof is being assembled by reduction_routes from both-operand retention plus a zero-input restriction.

2026-11-25T14:08:35.636631+00:00 counterexample_search: After root renewed the lease, started a fresh 20-minute search with exactly two active NOT gates. Sources and output are now written directly to results/orch/search/ so they survive checkpoints. Complete earlier computational evidence has also been copied there; none is a Lean-checked lower bound.

2026-11-25T14:09:54.949757+00:00 reduction_routes: full Restriction companion compiled exit0 against full Structural16. Then Floor17Live.lean proved 17 <= k for signed semantic Live runs starting from Petersen inputs; Floor18.lean proved 18 <= k+1 when first normalized binary operation is not OR. Both actual full-module Lean checks exit0 (only unused simp warnings). Standalone Structural17.lean with circuit translation currently compiling.

2026-11-25T14:11:28.394655+00:00 or_first_bound: OrFirst.lean companion kernel-checked via OrFirstPackedTest.lean, exit0, empty stdout/stderr. Packed4000-slot witness table proves retained distinctpin c after firstOR(a,b) followed by any signed binary gate combining OR(a,b) and c (2,880 valid cases). Original list-table proof attempt exited137, packed replacement succeeds. Self-contained OrFirstStandalone.lean prepared with allowed PEqualNP.Defs import, awaiting full compilation. Nine-input15-signed-binary CGP search300s found no exact circuit after1,879,000,000 mutations; best3errors, only heuristic evidence.

2026-11-25T14:11:48.455235+00:00 reduction_routes: full reusable Floor17Live.olean and Floor18.olean emitted under /tmp/oec/pequalnp-pilot-93/, both exit0. First-OR agent notified. Structural17.lean standalone 4984 lines/307046 bytes includes all certificate sources and public exact plain-input extractor; full compile still running.

2026-11-25T14:12:13.954772+00:00 root: latest lease expiry 2026-11-25T14:32:13.496Z; current full lease state in scratch lease-current.json. Only root renews.

2026-11-25T14:14:46.130980+00:00 or_first_bound: OrFirstAlgebra.lean compiled exit0 with empty log; bin identities simplify (a OR b) AND NOT a to b AND NOT a, and or_difference_front moves this second operation before OR or deletes unusedOR. OrFirstFloor.lean compiled against full Floor18 modules, exit0 with empty logs; firstOrDifferenceFloor yields18 binary gates, firstOrDifferenceDropFloor yields19 when initialOR signal is not retained. Exact logs or-first-algebra-olean2, or-first-olean2, or-first-floor2 in scratch. Companions frozen; combined standalone still compiling.
