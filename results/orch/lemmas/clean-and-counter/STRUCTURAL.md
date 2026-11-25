This is a counterexample search for L-meta-1904. No counterexample has been found.

The first construction starts with a core graph H. For every minimal vertex cover C of H, supply the clause OR(C) as the neighbor OR of an added star center. Since the edge function of H is the conjunction of these clauses, this supplies a way to reuse OR gates in an AND circuit that can have unsafe intermediate gates.

This construction is severely restricted by the girth assumptions. If a core vertex v has two distinct neighbors u and w, extend {v} to a maximal independent set. Its complementary minimal vertex cover contains both u and w. The new center attached to that cover then forms the 4-cycle v-u-center-w-v. Consequently H must be a matching, apart from isolated vertices. A matching with at least three edges has two distinct minimal covers sharing at least two vertices; their attached centers also form a 4-cycle. Thus only matchings with at most two edges survive in this construction family.

The script cover_extension.py exhaustively checks every labeled core graph through six vertices. For each core with no triangle or 4-cycle, it constructs all minimal covers and the attached-center extension. The surviving extensions are exactly those predicted above. This computation is supporting evidence for the informal argument, not a Lean proof.

The two-edge matching example has eight vertices and ten edges. An unsafe circuit uses fourteen gates and has two unsafe intermediate ANDs. Its four core vertices form a vertex cover, and an explicit safe circuit uses only thirteen gates. Both circuits were checked on all 256 input assignments; every AND output in the latter circuit was also checked to imply the graph edge function. Complete circuit data, safety counterexamples for the former circuit, and girth checks are in matching-two-example.json. This example therefore does not refute the posted statement.

A related obstruction applies even when some clause centers overlap the core. A star's neighbor set is independent in a triangle-free graph. If every minimal vertex cover of H were supplied as such a clause, every minimal cover would therefore be independent. In a graph of girth at least five, an edge whose endpoints both have degree at least two extends to an induced four-vertex path a-u-v-b. Extend {a,b} to a maximal independent set; its complementary minimal vertex cover contains the adjacent vertices u and v, a contradiction. Hence such a residual H must be a star forest. This argument concerns the specified shared-clause construction, not arbitrary AND/OR circuits.

The separate program search19.cpp searches for a nineteen-gate monotone Petersen circuit. It starts with twenty-gate star-cover circuits and an earlier four-error approximation, and retains separate populations according to the number of active unsafe AND gates. Any candidate would still require a concrete lower bound for safe circuits before it could refute L-meta-1904. The code uses only AND and OR, ordinary ten-input circuit semantics, and an out-of-range false wire; it does not have the free seed from the previous task. Full truth-table checks are repeated independently by validate19.py.

Public GitHub searches did not locate a primary theorem resolving this question. No unverified literature claim is used in the arguments or computations above.

The theta(2,3,3) run uses vertices 0 and 1 as endpoints and paths 0-2-1, 0-3-4-1, and 0-5-6-1. A ten-gate approximation computes

    ((x0 OR x6) AND (x1 OR x5))
      OR ((x3 OR x1) AND (x0 OR x4))
      OR (x2 AND (x0 OR x1)).

Its only extra term is x0 AND x1. Since the endpoints together dominate every other vertex, the sole false positive is the assignment with exactly vertices 0 and 1 true. All 128 rows were independently checked. This is not a counterexample. The frozen circuit and exact error set are in theta233/one-error-candidate.json and theta233/one-error-validation.json.

The C7 search was stopped when root identified an accepted library theorem giving its exact bound; it is only an encoding check. No new C7 lower bound is claimed. Petersen19 was stopped after a plateau at four errors so that the single search core could move to theta(2,3,3).
