# Independent review: adapted upstream graph framework

Reviewed UTC: 2026-11-25T17:34:08.593161+00:00

Verdict: PASS for the stated graph-specific structural helpers, not a complete lower bound or solution of L-meta-9775. Source: 352 lines, 18,424 bytes, SHA-256 `8eed78acb6027b514de1d1d2bd21bf5259f39d7a629e65ebfb2cbe3954e714ff`.

The archived upstream source is byte-identical to Git commit `790ef40780fc680c09cde228f2229fe058bd6e08` at lean/PEqualNP/Outside/L_meta_9774.lean (SHA-256 `520735eab64913c4e1c8d0146abec81ef2c08c8a825a2c98b92f7dc86cd1454d`). Comparison of the declared upstream line ranges finds only import/namespace scaffolding, the exact graph edge and neighborhood replacements, and the corresponding side-neighborhood tables and witness indices. The generic weight API is unchanged. The complete comparison is preserved in upstream-graph-independent.diff.

I independently parsed the actual Lean edge list and 14 neighborhood bitmasks. They match the posted 19 edges exactly; the directed adjacency is their symmetric closure. All 16,384 truth assignments agree. The finite sem_Gr conditions hold: symmetric, loopless, no neighborhood included in another, and each vertex has a neighbor other than any prescribed vertex. Degrees are two or three; distinct common-neighbor sets have size at most one. Both side127/side16256 finite neighborhood partitions, pair separation, triple intersections, and explicit witness indices were checked independently.

`normalized` supplies all three premises of strict-live normalization on the full input domain: nonconstant output, output distinct from every individual input, and every input essential. Its witnesses are actual edge pairs and rejected singleton rows. `side127` and `side16256` retain the explicit Bzero=0 and exact ineligible-side premises; their conclusion Bplus>=12 is not asserted for arbitrary circuits. `projected_count` retains independent-set and cardinality premises. `compact_weight` requires a successfully validated finite weight certificate and its subset premise; no old weight table or final upstream theorem was imported.

Both archived graph compilation streams are empty and their hashes match the provenance metadata; export exit 0 is author-recorded. No build was repeated. Format scan found no prohibited proof markers, strings, or attributes; heartbeat limits are locally scoped. Auxiliary UpstreamDagTools import requires inlining before final one-file submission.
