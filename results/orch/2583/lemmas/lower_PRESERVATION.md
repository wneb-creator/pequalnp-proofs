# Lower-bound agent preservation status

Development stopped immediately when the root reported the 2583 renewal error. No own build or search remains active.

All five sources below compiled successfully with exit 0. Full stdout and stderr, including earlier failed attempts, are preserved under `results/orch/2583/logs/`.

- `lower_singleton_star.lean`: SHA256 `e0dc893c1dec5854ab2d2d3a154d7f6ad2b75dd4f53448add31aa95dfedf8c08`, 88 lines.
- `lower_four_clause.lean`: SHA256 `e34502d0c29a1279f4b4beae14247c787b75ee08496b38c4c2362daa2d9a0331`, 105 lines.
- `lower_four_clause_rel.lean`: SHA256 `b5e14267c46725e2f15db5e8420b14b5a85b03399bf0fc48c45f0d1fdb74039b`, 142 lines.
- `lower_four_clause_matching.lean`: SHA256 `fd90657793b294f5d82091acfd98d55c254eb2eaf66b229036e46935781be6df`, 190 lines.
- `lower_two_dirty_cycle.lean`: SHA256 `2b3a33d48c1bf007862e12da2b4e2176c4ca547bb8567e59fb9b1702a1f8ab37`, 93 lines.

`lower_singleton_star.lean` proves semantic singleton cross-star structure for arbitrary monotone factors whose conjunction lies below a C4-free graph function. It assumes neither READ1 nor any normal form.

The three `lower_four_clause*` files are successive checked versions. The final `lower_four_clause_matching.lean` subsumes the earlier two. Its public theorem `FourClause.clauses_ge_five_on_matching` applies to arbitrary point/line types and a rectangle-free incidence relation: a globally clean conjunction of OR-clauses accepting three disjoint incidences needs at least five clauses. It uses an explicit kernel-checked census of all 512 three-by-three matrices, with five independent assignments for the 21 valid matrices containing the diagonal. The theorem rules out three disjoint accepted edges in a clean AND of two independent dirty ANDs placed on opposite operands, including OR wrappers after distributivity. It does not establish a gate-cost replacement theorem, the same-operand case, or the dependent-gate case.

`lower_two_dirty_cycle.lean` is a checked boundary example. A ten-gate AO2 block lies below the C6 edge function, has exactly two dirty AND gates, accepts three disjoint incidences, and has a genuine three-variable prime implicant. It does not compute C6 by itself. Adding the missing edge yields a twelve-gate AO2 circuit computing C6 exactly, still not READ1. The file also checks an eight-gate READ1 star circuit for C6. No optimality claim is made. The failed first compile caught the earlier overly strong claim that the ten-gate block itself computed C6; the corrected successful file makes the weaker accurate claim explicitly.

Exploratory Python and C++ searches are preserved under `research/`. They are not Lean certificates. A dependent two-dirty candidate was found only as computational evidence for a globally clean block accepting three matching edges; it was not formalized before the stop. No conclusion about the full posted statement follows from these searches.

The posted L-meta-2583 statement remains unresolved: these partials do not prove cost-preserving READ1 normalization for arbitrary plane circuits.
