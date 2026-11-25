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
