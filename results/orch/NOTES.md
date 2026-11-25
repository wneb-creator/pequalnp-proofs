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
