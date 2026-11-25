# Existing-results audit for L-meta-2583

- Checked L_meta_7684 supplies a READ1 star-cover circuit of size at most |E|+|A|+|B|-1.
- Checked L_meta_4897 supplies the converse cover budget for an existing READ1 circuit on a C4-free bipartite graph. It requires READ1; it is not an unrestricted monotone lower bound.
- Checked L_meta_7639 specializes the READ1 lower bound using a perfect matching, yielding |E|+N<=size+1.
- General C4-free no-size-loss READ1 normalization is the unresolved L-meta-4895. Its reductions R_meta_4895_1, _215 and _628 all retain an unrestricted matching/cover charging premise; their construction and structured-read1 premises are checked.
- Thus plane normalization reduces to the unrestricted scalar bound N*(q+2)-1<=C.size. For q=2,N=7, a 26-gate monotone Fano incidence circuit would refute the statement; READ1 needs27 gates. For q=3,N=13 the threshold is64.
- Checked L_meta_3706 gives a cover bound with a deficit for edges satisfying Core.ReadTwiceAt. Checked L_meta_3700/L_meta_3653 handle exactly one junk AND under additional lifted normal-form assumptions; a general multi-junk block charge was not found.

## Checked construction partial

`lemmas/existing_star_builder.lean` copies L_meta_7684 under the target auxiliary namespace and adds:

- incidenceEdges_card: degree(q+1) on each line gives N*(q+1) edges.
- lineStarUpper: a correct AO2 READ1 circuit exists with size<=N*(q+2)-1, using all lines as the star cover.
- normalize_of_budget: if N*(q+2)-1<=C.size, the exact requested replacement conclusion follows.

The partial compiled with exit0. Complete stdout/stderr are preserved under logs. It does not establish the missing scalar lower bound, and it does not prove the full posted statement.

Recorded 2026-11-25T14:50:41.477993+00:00

## Checked cyclic Fano lower bound

`lemmas/existing_fano_lower.lean` copies L_meta_7639 under 2583_aux.FanoLower. It proves the cyclic incidence p=l or l+1 or l+3 in Fin7 has21edges, line degree3, unique joins, no rectangles and identity matching. `readOne_lower` proves every correct AO2 READ1 circuit has size at least27; `no_small_replacement` rules out a READ1 replacement of size at most26. Full source compiled exit0, with warnings inherited from the checked source. It does not assert that a26gate correct circuit exists. Full log5 is preserved under logs, and reusable scratch module ExistingFanoLower.olean is available.

Recorded 2026-11-25T14:55:34.985015+00:00

## Checked general sharp-bound equivalence

`lemmas/existing_plane_equivalence.lean` combines the frozen star-builder, FanoLower general cover theorem, and Geometry plane cover cardinality. Its new PlaneBound.readOne_lower proves every correct AO2 READ1 plane circuit has size at least N*(q+2)-1. PlaneBound.replacement_iff_sharp proves the exact replacement conclusion is equivalent to that size bound on the original circuit. PlaneBound.posted_iff_sharp states the full posted universal normalization statement verbatim on the left, equivalent to the unrestricted AO2 sharp lower bound. This equivalence does not settle the missing unrestricted lower bound. Source compiled exit0; log2 is preserved under logs; reusable scratch module ExistingPlaneEquivalence.olean is available.

Recorded 2026-11-25T14:58:16.623208+00:00

## OR-count audit

No checked unrestricted theorem |E|-1<=nOr was found in complete filename censuses for nOr/countOrGates/orCount/OrCostLB, followed by final-statement and relevant internal-theorem inspection.

- L_meta_984 contains an exact circuit-to-OR-cost bridge `OrYF.or_bound_of_eval_eq`, plus finite graph certificates for 31 graphs on at most7vertices. Its generic calculus permits free ANDs and counts ORs; `paidVertexYF` saves one OR on vertex deletion, and `paidLeafYF` propagates the exact |E|-1 bound through degree-one deletion. It does not give the desired arbitrary C4-free bound. Its header mentions max-degree-two bases but the inspected generic declarations only establish zero/one/two-edge bases and leaf peeling; finite state tables carry the harder cores.
- R_meta_2280_37 leaves the Fano free-mixed-input-OR residual19OR lower bound as a hypothesis, not a checked consequence.
- L_meta_5274 proves only18OR for certain q3 boundary tests, much weaker than51OR and not an exact general statement.
- L_meta_7241 proves the full |E|+cover<=size+1 bound for an exact AO2 C4-free graph circuit under the extra condition that EVERY AND gate is false on EVERY nonedge pair. It does not assume READ1. This is the strongest clean applicable structural restriction found.
- L_meta_4915 proves HasSharedBlockCost G c -> HasBlockCost G c for C4-freeG: OR sharing cannot reduce the block-cover optimum. It does not convert arbitrary AO2 circuits into block circuits.
- L_meta_7862 provides general least-circuit TopForm accounting with a Ustar deficit; it is not the sharp unrestricted bound.
- L_meta_3760 andL_meta_8725 rule out exactly one junk AND in a least bipartiteC4-free circuit; two-or-more junk gates remain possible.
- L_meta_4849 refutes automatic pair-cleanliness of allAND gates in a globally minimal triangle/C4-free circuit, using an8vertex,8edge,11gate witness. The witness graph contains cycle0-4-7-1-6-0, so it is NOT bipartite and does not refute a bipartite-specific normalization.
- L_meta_2969,L_meta_3444,L_meta_3446 refute proposed core-charging inequalities on exact bipartiteC4-free circuits; semantics agent is auditing their concrete witnesses.

Full census and final-statement outputs remain in scratch2583-existing-*files.txt/*statements.txt; no theorem was inferred from a boundary-only statement.

Recorded 2026-11-25T15:01:03.379661+00:00

## Checked local three-clause pruning

`existing_three_clause.lean` is a new standalone semantic lemma, not copied from an Outside proof. A clean block OR(Ppoints) AND OR(Llines) AND (OR(Rpoints) OR OR(Rlines)) has at most one possible point center in P intersectionRpoints and one line center in L intersectionRlines, assumingbothP,Lhavesizeatleast2 and incidence isC4free. The two corresponding star terms form a function below the original block and agree on every point-line pair. Fullcompileexit0; log1preserved. This does not yet provide circuit rewiring or a gate-count bound.

Recorded 2026-11-25T15:07:31.281845+00:00

`existing_three_clause_context.lean` extends the frozen84-linepruningfile with Hits/Pruned monotonicity and a generic monotone-context substitution theorem. If h<=g, h is monotone, h andg agree on every incidentpair, and a monotone contextK withg computes the exact quadratic incidence function, then the samecontextwithh computes it too. This explicitly permits higher minterms in g; they may shrink safely. The theorem is semantic, without a circuitrewiring or size claim. Fullcompileexit0 andcontextlog1preserved.

Recorded 2026-11-25T15:08:03.372480+00:00
