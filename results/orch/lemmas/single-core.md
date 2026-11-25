# L-meta-2962 single-core investigation

- Checked 2026-11-25: `exists_edge_cover_card_le` selects a vertex cover of any finite edge family with cardinal at most the number of edges.
- Checked: `core_cover_singleton_incidence` proves the posted conclusion when each maximal core accepts at most one edge. It permits arbitrary cone overlap and needs no bipartiteness, C4-free, semantic, or lift-fixedpoint assumptions.
- Proof: Dcard <= maximal-core count <= union-of-cones cardinal; select at most Dcard endpoints and use the checked generic deleted-edge cover extension.
- Source additions: `/tmp/oec/pequalnp-pilot-71/single-core/extra.lean`; combined checked source: `SingleCore.lean` in that directory.
- Validation: `lake env lean /tmp/oec/pequalnp-pilot-71/single-core/SingleCore.lean` exited 0 with empty build.log. Parent notified immediately for preservation push.
- Open: handling a core accepting multiple edges; a single maximal core need not have a star-shaped accepted-edge family (an implicant computing several stars can be ANDed with the OR of their centers).

## Checked union-of-cones leaf bound

- `LeafUnion.lean`, namespace `PEqualNP.Outside.L_meta_2962_aux.Leaf`, adapts previously checked cone connectivity and wire-dependency lemmas from LeafBound/ReadTwoBridge using only Mathlib and PEqualNP.Defs.
- New `union_leaf_count`: any finite family M of valid gate outputs has at most |union cones| + |M| distinct input wires read inside its cones. Proof counts operand slots: every non-output gate consumes one distinct slot wire, leaving the stated budget for input wires. Overlap is handled without disjointness assumptions.
- New `core_endpoints_leaf_bound`: all vertices incident to accepted edges D obey |vertices(D)| <= |U| + mc. Each endpoint is essential to its implicant core because a singleton cannot satisfy a graph edge function.
- Validation: `lake env lean /tmp/oec/pequalnp-pilot-71/single-core/LeafUnion.lean` exited 0, no warnings or errors. Full output empty.
- This handles the circuit part of the target when D is a star forest, since then |D| + tau(D) = |vertices(D)|. That graph specialization is not yet formalized. For general D it does not close the edge-plus-cover bound.

## Checked matching case

`core_cover_matching_incidence` proves the posted conclusion when D is a matching. It allows every core to accept many edges and arbitrary overlap between core cones. The graph endpoints have cardinal exactly 2|D|, so the checked leaf bound pays for one endpoint per edge plus all edges. Combined `Matching.lean` compiles with exit 0 and empty stdout/stderr. This remains a special case, not the full posted theorem.
