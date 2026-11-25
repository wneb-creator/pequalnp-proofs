# Combinatorial work for L-meta-2583

The ReadK notion is per-prime-implicant proof-tree multiplicity; it is not a global bound on how many gates read an input.

Existing results:
- L_meta_7684 constructs a read-1 AO2 circuit from any bipartite vertex cover, at cost at most edge count plus cover cardinality minus one.
- L_meta_4897 proves the matching lower bound for read-1 circuits on C4-free bipartite graphs.
- L_meta_7639 specializes that lower bound to a graph with a supplied perfect matching.
- L_meta_2393 contains plane point regularity and cover counting helpers (starting at lines4806 and4977), though its full theorem is a concrete junk-free normalization result.

The unchecked central difficulty remains removing the read-1 premise from the exact lower bound. For a plane the star upper bound is N(q+2)-1, and geometry forces every vertex cover to have at least N vertices.

## Compiled geometry component

`lemmas/PlaneGeometry.lean` imports only PEqualNP.Defs and compiled with exit0, empty stdout/stderr. Namespace `PEqualNP.Outside.L_meta_2583_aux.Geometry`.

- `lines_through`: every point lies on exactlyq+1 lines, from the posted incidence hypotheses.
- `edge_count`: the incidence pair finset has cardinality N(q+1).
- `no_rectangle`: the incidence relation is C4-free.
- `cover_lower`: every bipartite vertex cover has at leastN vertices, using regularity and incidence counting.
- `hall_condition`: each point set has at least as many neighboring lines.
- `plane_data`: packages point regularity, edge count, and the cover lower bound.

Regularity and incidence-count templates were adapted from L2393. Its unavailable bipartite summation theorem was replaced by elementary `Finset.sum_comm`, preserving the posted single import. Mathlib Hall matching theorems are not currently imported by Defs, but an explicit perfect matching is unnecessary because cover_lower feeds L4897 directly.

Artifact: 155 lines, 7064 bytes, SHA256 ba2df371d6d92b69d37c3fc019e7e594b424e19c33cd6d3d5111397ef85d10b0.
