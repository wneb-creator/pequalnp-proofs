# Independent review: Public4293

Verdict: PASS for the conditional slot-count contradiction. It requires
both displayed slot-cardinality bounds; the finite-code implication
supplying those bounds is a separate wrapper under review elsewhere.

Reviewed source: 73 lines, 3,281 bytes, SHA-256
`8029db2ea407f35996febfb335ed32f4345a9ab0465f4a98e942122812c6b722`.
Both complete scratch `9775-public4293-001` logs are present and empty;
the author reports successful checked compilation and export. No build
was rerun for this review. The source records the strategy's attribution
to Thomas Brovelli (`ithurtstom`), public PR 18338 at the stated head;
this review audits the local specialization, not a separate exact-copy
claim about that external source.

`assigned_mem` correctly puts an ineligible vertex's assigned input arc
in each neighboring vertex's exit set. `assigned_private` uses the
opposite arc's singleton support to show that it can belong to `W(x)`
only for that ineligible vertex itself. Neither helper assumes a final
lower bound. `two_slots` is the direct finite-set fact that two distinct
members exhaust a set of cardinality at most two.

Mask 4293 contains vertices 0, 2, 6, 7, and 12. The main proof uses only
the required membership of 0 and 12. The assigned arc of 12 belongs to
`W(5)`. The edge witnesses for 5–10 and 5–9 also belong to `W(5)` and
are each distinct from that assigned arc, because their opposite arcs
belong to `W(10)` and `W(9)`, respectively, contradicting private support
if equal. The bound `card(W(5)) <= 2` therefore identifies those two edge
witnesses.

In `W(10)`, the assigned arc of 0 and the opposite arc of that common
edge witness are distinct. `sem_cover_free`, instantiated with the
nonedge 8–9 and edge 10–4 (where 4 is adjacent to neither 8 nor 9), gives
a third candidate arc whose support excludes both 8 and 9. It cannot be
the assigned arc of 0, which contains neighbor 8. The bound
`card(W(10)) <= 2` therefore identifies it with the opposite common
edge arc, whose support contains 9 from the 5–9 witness. This is the
explicit final contradiction. All finite adjacency premises match the
exact new 19-edge graph.

The theorem assumes `StrictLive`, exact graph semantics, the actual
ineligible-mask equality, and the two slot bounds. It does not silently
assume `Bzero = 0`, and it does not conclude that mask 4293 alone is
impossible. The only option is `maxHeartbeats`; there is no new axiom,
`sorry`, `native_decide`, forbidden root marker, string literal, or
attribute. Final scratch-import assembly/checker requirements remain.
