# L-meta-3678 orchestration notes

Root holds the only lease. No agent may call the desk.

Posted statement: least AND/OR circuits for bipartite graph edge functions can have AND-depth one. Exact statement is in scratch desk-first.json. Allowed project import PEqualNP.Defs; final proof must use own helper namespace.

Strategies: normalization, counterexample search, existing lemma search, checker/status review. Toolchain setup is in progress. Append concise findings under your agent name and UTC time.

## Counterexample checks 2026-11-24T17:11:36.193833+00:00
Exact breadth-first truth-table circuit enumeration completed for all bipartite graphs with at most four vertices (all 16 labeled 2x2 graphs and all star subgraphs). General AO2 and AND-depth-one minimum gate counts agree. For 2x2, counts range 0 to 4, with three-edge paths requiring 4. Computation only, not Lean checked. Script and complete log: /tmp/oec/pequalnp-pilot-36/counterexample/small_bfs.py and small_bfs.log. InCone is explicitly strict; no reflexivity loophole. Python has SciPy MILP but no z3/pysat/OR-Tools; C++ compiler available.

## lemma_search 2026-11-24T17:11:40.419610+00:00

Checked source routes: L_meta_1501 normalizes to TopForm at fixed least size and fixed junk count; L_meta_1499 strictly decreases andPairs when the lower AND is BelowF. Neither removes junk ANDs. L_meta_1733:3957 proves existence of a least AO2 circuit by Nat.find. Candidate scratch lemmas/Least.lean now contains least existence, least choice minimizing andPairs, and the equivalence of andPairs=0 with the target no-stacked-AND condition; awaiting prepared dependencies to verify.

## proof_restriction — 2026-11-24T17:13:34.409707+00:00

Read Jukna 2006, Disproving the Single Level Conjecture, author manuscript https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (read 2026-11-24). The general quadratic-function separation uses non-bipartite saturated extensions, so does not refute this gap. The manuscript explicitly distinguishes graph representation (correct only on cross pairs) from exact quadratic-function computation. No bipartite exact size-preserving normalization result located.

Global restriction obstacle: splitting a mixed-color OR network into left/right projections need not preserve gate count because sharing can be lost. For M_i=x_i OR y_i, computing many pairwise M_i OR M_j costs n+t gates whereas separate projected pair sums can cost 2t. Crown graph candidate F=(OR x_i) AND (OR y_i) AND T2(x_i OR y_i) is exact, but current gate accounting does not beat the flat construction.

## Counterexample checks 2026-11-24T17:13:45.315024+00:00
Extended exact circuit BFS to all 64 labeled bipartite graphs on parts 2+3. General minimum and AND-depth-one minimum agree for every graph; maximum 5 gates. Depth-one enumeration tracks a syntactic has-AND bit per stored wire, so it does not infer depth from semantics. General search visited 896104 size-5 function sets, flat search 837724 decorated sets. C++ source small_bfs.cpp; complete outputs bfs5-general.out and bfs5-flat-exact.out are byte-identical. These are computational checks only, not Lean checked. CaDiCaL source cloned from official GitHub and compiling to support larger finite searches.

## proof_normalization 2026-11-24T17:13:53.397976+00:00

Existing L_meta_1501 establishes TopForm at least size, but this only removes nesting whose lower AND is BelowF; L_meta_1499 decreases andPairs while preserving junk count. Dirty AND elimination remains the obstacle.

Local obstruction: ((a OR d) AND (b OR c)) AND ((a OR c) AND (b OR d)) computes matching ab OR cd. Both lower conjunctions are dirty, and naive operand deletion fails. The seven-gate circuit is not least (three gates suffice), so this is not a counterexample to the target.

Lean-checked scratch LocalNormalization.lean gives this identity, dirtiness witnesses, and a biclique color lemma. Root notified for push-early preservation.

Primary research read 2026-11-24: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Its total-size separations use non-bipartite saturated extensions. They do not refute our exact bipartite statement. Cross-pair graph representation is weaker than exact graphFun computation because larger independent sets matter.

## lemma_search 2026-11-24T17:15:01.611771+00:00

Scratch lemmas/Least.lean passed `lake env lean` with exit 0 and no warnings. Ten helpers establish least existence, least choice minimizing andPairs, equivalence of zero pairs with no stacked ANDs, monochromatic and singleton rejection, the edgeless case, normalization conditional on strict pair-count descent, and the at-most-one-gate case (root contributed the latter). This is a checked partial only: the bipartite descent obligation remains open. Root notified immediately for review and early push.

## Counterexample candidate 2026-11-24T17:22:17.722069+00:00
Tarjan-derived graph constructed explicitly: vertices0..10 are original linear-family inputs;11..24 private per-output inputs;25..38 selectors. Edge list has64 edges, all cross0..24 to25..38. Circuit58 gates, output96. Python minimal-monomial antichain evaluator confirms exactly these64 quadratic minterms. Data/generator: scratch counterexample/tarjan_graph.json and tarjan_graph.py. Initial TarjanGraph.lean size58/AO2/bipartite lemmas compile; generic graphFun_edgeGraph_list in EdgeGraphHelper.lean also compiles. Full upper equality in TarjanFull.lean is being finished by explicit Boolean absorption and distribution. No lower-bound proof yet, so this is candidate refutation only.
