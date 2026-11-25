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
