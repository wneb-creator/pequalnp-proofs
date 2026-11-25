# L-meta-1735 shared notes

Lease obtained 2026-11-25T04:34:32.013Z; initial expiry04:54:32.013Z. Only root holds and renews this lease. Prior L-meta-2602 lease invalidated with410; its results remain preserved.

## 2026-11-25T04:38:52.742325+00:00 Independent statement/definition audit

The posted statement has no immediate vacuity or indexing loophole. IsLeastAO includes AO2 validity, exact graphFun semantics and global least size in that same no-constant binary AND/OR model (repeated inputs allowed). TopForm forbids clean AND ancestors of later ANDs; it permits arbitrary dirty nesting. Ustar is exactly the graph edge finset minus direct OR-reachable top crosspairs. The universal constant is independent of n and the graph, so a coarse total-edge lower bound would suffice; essential-input support alone gives no linear edge bound for girth-five graphs. A star construction bounds minimum size from above and cannot be reversed. Direct separated-polynomial charging is invalid on the C4-free path ab,bc,cd, since (ab)(cd) contains bc. No proof or refutation follows from this audit.

Assignment preservation PASS: statement.txt exactly matches the scratch statement, 386 bytes, SHA256 e96bcbe4765a13c9a132aa05e35e03a5597189069f7718064865e1fb6b92575f. Initial notes/timeline/validation accurately distinguish the new lease from the archived L2602 work and claim no checked result yet.

UTC 2026-11-25T04:39:35.255976+00:00

## Library composition audit — lemma_route

No complete assembly is presently available in the checked source census. The fresh public map confirms 1735, 1768, 1770, 1882, 2076 and 2579 remain conjectures.

- R1735_1 partitions by junk: L1876 closes empty junk (717 lines); L1878 closes singleton (952); new L1880 closes arbitrary pairwise-incomparable junk (786). Its remaining general nested-junk premise is L1882. R1882_1 reduces that case to support bound and failure of a four-vertex neighborhood cover. L5242 (1288 lines) only closes exactly two nested junk gates with that cover failure. It does not cover three or more.
- R1735_5 reduces to support size and a bound on the 3-core of G.deleteEdges(starEdges G C). L2074 (222 lines) proves support.ncard <= size+1 exactly. Core target L2076 remains conjectured, with reductions R2076_1 and R2076_389 into dirty witnesses versus directly charged star edges.
- R1735_7 reduces to a branching OR-side pattern and residual edges. L2577 (40 lines) proves the branch bound <= 2*size exactly. Residual target L2579 remains conjectured. R2579_2 splits broad OR-neighborhood patterns (proved by L5122, 453 lines, <= 12*size) from a residual graph core. R2579_415 gives a different pair-bank charge <=24*size plus unresolved small-bank core. R2579_1 splits centreless / one-sided / two-sided tops; no checked complete residual theorem found.
- L1766 (705 lines) gives the general Ustar witness split into a top with endpoint in one raw OR side plus a firing junk on the other, or distinct firing junk gates on both sides. This feeds missing L1768/L1770. Accepted L3805/L3807 prove those subcases only with junk>=3 and every pair of junk incomparable.
- L1880 internally bounds all graph edges by a universal gate constant under its parallel-junk condition. Its proof assigns AND ranks at most two; the uniform rank cap depends on no nested junk. It cannot currently be applied to arbitrary TopForm circuits.
- R606_{2,3} routes toward coarse graph-edge lower bounds use normalization plus a Ustar bound; importing this would be circular.

Header census: scratch 1735-ustar-headers.json (78 entries) and 1735-ustar-paths.txt. New-main headers checked against upstream d7dd149881faedf1819d7ca0ca51130327f5a9bb; among its 182 new files, L1880 is the only new Ustar/girth5-size main theorem.

## 2026-11-25T04:41:47.007497+00:00 Independent review: exactly two nested dirty ANDs

PASS: nested_two.lean, 1635 lines, SHA256 4f9d8a97a1ab824b7ebe3d526ae1cea106f7e753481360866444e6cf624de120. Support foundation is verbatim L2074 after namespace rename; TwoJunk foundation is verbatim L5242 with its final target omitted; neighborhood counting is verbatim R1882_1 except trailing newline. The final composition gives Ustar.card <= 4*(C.size+1) under girth at least five, IsLeastAO, TopForm, exactly two junk gates and a nested pair. It does not establish the universal target. The four-center neighborhood cover is combined with the graph-support bound, and the graph edge-nonempty premise is not needed for this subcase. Build completed with only three unused-binder warnings; separate axiom audit reports only propext, Classical.choice and Quot.sound. Before canonical integration rename the three helper theorem declarations to lemma and place the standalone Support declaration inside the auxiliary namespace block. All other static restrictions pass; imports are narrowed and no global options occur.

UTC 2026-11-25T04:41:55.248458+00:00

### Concrete composition completed
L5242 is stronger internally than its negative-cover main statement: `Final.cover` gives an actual set K of at most four vertices with every Ustar edge incident to a neighbor of K, under exactly two nested junk gates. No missed edges are needed. The girth-5 counting in R1882_1 bounds those edges by |K| times support.card. Combined with L2074 this yields explicit c=4, independently compiled in `lemmas/nested_two.lean` (1635 lines; SHA256 4f9d8a97a1ab824b7ebe3d526ae1cea106f7e753481360866444e6cf624de120). Axiom audit: propext, Classical.choice, Quot.sound only. Independent review PASS.
A separate `lemmas/at_most_two.lean` assembles this with L1880 internal edge_bound. The latter applies to all incomparable-junk circuits, including zero and one junk gates; therefore at-most-two total junk can be bounded without separately copying L1876/L1878. This is a restricted result, not full L1735; arbitrary three-or-more nested junk remains unresolved.
