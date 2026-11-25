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

## Checked strict shared-cone leaf bound

- `LeafUnionStrict.lean`, namespace `PEqualNP.Outside.L_meta_2962_aux.StrictLeaf`, strengthens the previous bound by removing the number of cores entirely.
- `core_family_leaf_count`: for ANY finite family M of cores in an AO2 circuit, all distinct input wires occurring in their cone union U have cardinal at most |U|. No maximality, bipartiteness, C4-freeness, exact output semantics, or lift-fixedpoint assumption is needed.
- `core_family_endpoints_count` and `maximal_core_endpoints_count`: |vertices(D)| <= |U|.
- New argument: when adding a cone that shares an old gate, the first entry into the old cone union names an old gate wire in a new operand slot. Every fresh non-output gate also consumes a slot, leaving at most one new input per new gate. A cone sharing no old gate uses the previously checked strict single-core leaf bound from its repeated-read witness.
- Kernel validation: lake env lean exited 0, stdout/stderr empty. Source saved with validation record for immediate preservation.
- This still does not imply |D| + tau(D) <= |U| + mc for general D; graph-edge density beyond vertex count remains the obstacle. It does settle the circuit side for star forests.
