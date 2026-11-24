# Theory route: L-meta-2028

Started 2026-11-24 15:15 UTC.

The exact statement negates the C4-free edge-function lower bound |E| + tau - 1. No immediate definitional loophole: Monotone2 is genuinely AND/OR, fan-in at most two, and IsVertexCover is the usual finite cover.

Existing reductions R_meta_612_1, R_meta_612_2, R_meta_612_7 distinguish acyclic/cyclic, block extraction plus star counting, or separate OR/AND gate counts. Any improvement over the usual cover construction must exploit multilevel operations; C4-freeness disallows two centers sharing a pair of neighbors, so pure side-OR sharing cannot help.

L_meta_1006 gives an 11-variable, 16-edge, C4-free graph with cover at least 7 and a boundary-only circuit using 6 ANDs. Expanded using fan-in-two OR gates, the given construction costs 20 gates against a proposed exact minimum 22. It is not an edge-function circuit: 39 truth-table mismatches; missing edges are (4,10),(5,9),(6,7),(6,10),(7,9),(8,9). The reusable gate is (x7 OR x10) AND (x6 OR x9), which also accepts the forbidden pair (9,10). Its high-degree residual terms cannot simply be output.

Searching input-identification quotients of that circuit: collapse all 678570 partitions of its 11 inputs; accept only homogeneous quadratic results whose graph is C4-free; count the surviving circuit after truth-table-based semantic common-subexpression elimination and dead-gate elimination. Script and complete log under /tmp/oec/pequalnp-pilot-31/theory/quotients.py and quotients.log.

Input quotient search finished: 678,570 total partitions; 61,670 homogeneous quadratic cases; 731 C4-free cases; no improvement. Extended search allowing both constants and all identifications: 23,430,840 substitutions; 778,873 homogeneous quadratic cases; 319,924 C4-free cases; no improvement. These are substitution counts, not distinct graph isomorphism classes.

Started a C++ evolutionary repair at 21 gates for the exact 11-variable graph, testing its 16 edge inputs and 24 maximal independent sets (40 bits). Correctness on those boundary assignments suffices for a monotone network, but any candidate is independently tested on all 2048 assignments. Best reached one missing edge (0,10), giving an exact circuit for the graph with that edge removed; that graph has tau=6 and target20, so no counterexample. Parallel SAT agent is testing repairs.

A separate finite search replaces any one of the original 20 gates by an arbitrary AND/OR of earlier wires and optionally adds one top AND/OR gate with an earlier wire. It derives the candidate graph from positive pair assignments, tests C4-freeness and cover size, then verifies full truth tables for potentially improving candidates.

Primary literature read 2026-11-24: Stasys Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Theorems2.1/2.2 construct saturated extensions of Sylvester/Kneser-type bipartite graphs: both vertex parts become cliques. Thus the published separation does not directly yield a C4-free example; any clique of size4 already violates the condition. The abstract confirms unrestricted monotone quadratic circuits can be substantially smaller than single-level circuits in general, so a generic star-normalization proof cannot be assumed without C4-freeness.

The one-gate dynamic graph census finished578,280 variants,9,507 C4-free pair-graph cases and no candidates with enough edge-plus-cover cost to beat surviving gate count. C++ fixed-target repair ran300seconds/1,666,000,000 evaluations; best still one missing edge.

New dynamic-search near witness:18live gates on a C4-free11vertex graph with15edges,tau5,bound19. All edge pairs accepted, but15 independent inputs are false positives inside maximal independent set mask363. Full pruned snapshot is theory/dynamic-snapshot.json in scratch; localSAT repair delegated to counterexample_search. Exhaustive input restrictions/identifications started on this new candidate.

BoundaryComplete.lean was compiled with pinnedLean4.36 at approximately15:27UTC, no diagnostics. It proves independent-set extension and the exact sufficiency of edge-pair positives plus maximal-independent-set negatives for an arbitrary monotone Boolean function. Parent notified immediately to preserve the result.

The dynamic near witness cannot be repaired merely by adding graph edges: its minimal bad inputs are {0,5,8}, {1,5,8}, {3,5,8}, {5,6,8}; every possible pair contained in each triple individually creates a C4 in the existing graph. For example adding(0,5) creates0-2-9-5-0, adding(0,8) creates0-2-7-8-0, and adding(5,8) creates5-8-7-9-5. This exhausts all pairs of the first bad triple, so no C4-free supergraph on these vertices can absorb that triple.

Dynamic near-witness substitutions finished23,430,840 cases,628,449 homogeneous quadratic outcomes,262,398 C4-free outcomes; no improvement. First dynamic run completed54,728,719 mutations in300seconds with no exact counterexample. A second run reverses preference toward exact graph functions (bad-constraint weight5, gate-deficit weight1), seeking an improvement from tight circuits.

Computed finite structured candidates independently: line graph of Petersen has15vertices,30edges,tau10,C4-free,target39. Orthogonality polarity graph ER3 has13vertices,24edges,tau8,C4-free,target31,4triangles and35maximal independent sets, so59 boundary tests suffice. Explicit JSONs saved in scratch and shared with the random search agent. ER3 decomposes as a subdividedK4 (4absolute points,6edge vertices) plus a triangle on3vertices, each joined to the two edge vertices of one perfect matching, and3edges joining those paired edge vertices.
