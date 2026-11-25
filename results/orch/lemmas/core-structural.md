# L-meta-2962 structural work

Checked Lean component: `/tmp/oec/pequalnp-pilot-71/structural/DeletedCover.lean`. `lake env lean` returned exit 0 with empty output; complete output file `structural/deleted-cover-build.log`.

Three generic graph-side lemmas, using only Mathlib imports:
- `cover_extension`: if S covers deleted edges D and Tprime covers G-D, then S union Tprime covers G.
- `minimum_cover_delete_bound`: a minimum cover T of G satisfies card T <= card S + card Tprime.
- `core_cover_of_certificate`: a cover S for D satisfying card D + card S <= card U + mc implies the posted numeric inequality.

This isolates one sufficient circuit certificate. It is stronger than the target and may be too strong: core outputs may have higher-support implicants containing edges outside D, and residual graph edges may share cover duties with D. No proof of the certificate yet.

Core definitions: coneSet includes the core gate itself; IsCore requires NOT BOTH operands to be implicant gates, rather than neither. Maximal cores range over dead gates too, while lift-fixedpoint constrains only output cone.

Relevant existing refutations: L_meta_3446 disproves analogous bound using only private core-cone gates; L_meta_2969 disproves companion outside-cone count; neither directly refutes current unfiltered U bound.

Structured search: glued P4 deadcore gadgets with globally deduplicated gate expressions. Script structural/glue_p4.py, output structural/glue-p4.log. Minimum observed margin zero; no negative candidate. Parent requested second route: 5-minute evolutionary mutations seeded by P4, fixed random C4-free bipartite graphs n=6..9, exact truth-table below-F and exact read-once pair mask, score uses target tau(G)-tau(G-D). Script structural/evolve_core.py, output structural/evolve-core.log. Currently running.

Completed larger tight-tree gluing search: 488,192 candidate additions across 30,000 random C4-free bipartite graphs (up to20 vertices), 17.96seconds, no negative margins, minimum0.

Useful pair-sharing identity: for two individually tight cores, union margin equals shared-edge count + tau(G1)+tau(G2)-tau(G1 union G2) minus shared-gate count. Thus a counterexample needs shared DAG gates to exceed edge overlap plus cover overlap. Shared matching subcircuits can exceed their edge count, but ensuring both outputs are cores has so far imposed gate overhead canceling the excess.

Final structured search summaries:
- glue-p4.log: {"done": true, "count": 1246772, "best": 0, "seconds": 79.7976450920105}
- glue-trees.log: {"done": true, "count": 488192, "best": 0, "seconds": 17.95907473564148}
- glue-planes.log: {"done": true, "count": 2189703, "best": 0, "seconds": 108.55681133270264}
- evolve-core.log: {"done": true, "best": 0, "steps": 15498000, "seconds": 300.1360356807709}

No counterexample found in these searches. This is computational evidence only, not a proof of the universal statement. The sole completed Lean proof component on this strategy remains DeletedCover.lean.
# Disjoint-cone assembly checked at 07:03 UTC

`/tmp/oec/pequalnp-pilot-71/structural/DisjointAssembly.lean` compiles with `lake env lean` and an empty final build log. It contains:

- `disjoint_cost_assembly`: local inequalities `card (D i) + card (S i) ≤ card (U i) + 1` sum to the corresponding union inequality when the `U i` are pairwise disjoint. Edge and cover unions need not be disjoint.
- `union_covers_deleted`: the union of local covers covers the union of deleted-edge sets.
- `cover_bound_of_disjoint_local_certificates`: these facts and minimality of the original cover imply the exact target inequality for a family of pairwise-disjoint cones.

This is a conditional assembly theorem, not a proof that actual circuit cores admit the local certificates or have disjoint cones. Those are precisely the unresolved hypotheses. No target file was edited.
