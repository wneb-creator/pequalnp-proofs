# Independent review: live DAG fork credit

Reviewed by constructive on 2026-11-25 UTC. Sources: `/tmp/oec/pequalnp-pilot-70/lower-bound/LiveDagCredit.lean` and its extension `LiveDagSupportBound.lean`. Read the full base and complete extension diff. The final arc-count and support-bound logs are empty; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS for the abstract counting and support-label statements.

The base counts parent-child arcs. Liveness covers every nonroot vertex in the child image. An arc entering a designated root adds a new image vertex beyond the nonroots; two distinct parents sharing any child make the projection from arcs to children noninjective. Either case supplies the extra unit. The upper bound uses the stated internal branching allowance and childless leaves. It correctly permits the shared vertex to be anywhere in the live DAG, rather than requiring it to be the exceptional leaf.

`labels_covered_by_leaves` uses strictly smaller child indices and support containment to reduce every live label to leaf labels. `extra_arc_double_leaf_bound` then bounds the union by the number of leaves plus one, allowing one designated label of size at most two and all other leaf labels of size at most one. The arc credit cancels that extra unit. The exceptional index need not be a leaf or present at all; the resulting weaker upper bound remains valid in those cases.

The support wrapper explicitly requires children to stay in the live vertex set and decrease in index. No acyclicity assumption is silently inferred from the raw arc count. Applying this result to the proof circuit still requires constructing the selected certificate DAG and proving liveness, branching charges, and a fork or incoming-root arc. Those are not conclusions of this helper.

The forbidden-format scan of the extension returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import is `PEqualNP.Defs`.
