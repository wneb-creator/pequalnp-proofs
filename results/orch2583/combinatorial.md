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

## Added-clause block geometry

A block of the form ((OR A AND OR B) OR OR C) AND OR D, with nonempty C, can be oriented from its rejection of the all-points and all-lines assignments. C and D lie on opposite sides, and one of A or B lies entirely on C's side. With A,C on the point side, split B into Bp and Bl. The accepted incident pairs are

    E = (C union (A intersection Bp)) product D
        union A product (D intersection Bl).

`RectangleCover.lean` proves that every C4-free rectangle has a star cover whose edge count plus cover cardinality is at most the sum of its side cardinalities. Unioning two such covers gives the same bound summed over all four sides. This yields a cover of E with cost at most |A|+|Bp|+|Bl|+|C|+|D|, directly accounting for the added-C shape.

`BlockGeometry.lean` checks the side-orientation proposition and the fact that if A,D each have at least two vertices, then C and the possible shared-support intersections have cardinality at most one.

`BlockDichotomy.lean` strengthens this to all sizes when C is nonempty: either D has cardinality at most one (a line-star); or C is a singleton and both A intersection Bp and D intersection Bl have cardinality at most one; or C is a singleton and A is contained in C, in which case E equals C product D (a point-star). The middle case is exactly what prevents a nontrivial OR subcircuit from being shared between the three clause supports A,B,D. The semantic agent has separately checked a three-support OR counting bridge and is assembling circuit replacements.

All three artifacts import only PEqualNP.Defs and compiled with exit0 and empty stdout/stderr. They establish finite block geometry; they do not prove arbitrary block decomposition, full circuit normalization, or the posted gap.

RectangleCover.lean: 80 lines, 3794 bytes, SHA256 85a6f2c9c12e09c33d6426af3500eff94ddcd031f303b63373f17285d9df8593.

BlockGeometry.lean: 143 lines, 6926 bytes, SHA256 41120dd6b71a8950eeb504cc3b5bc511a164423989759fe44d53c68728908ed6.

BlockDichotomy.lean: 204 lines, 9753 bytes, SHA256 ac7cd4a608b4c904916f6e8e0034180dc4b295f99809c1903b406f7ef9f3ce0f.
