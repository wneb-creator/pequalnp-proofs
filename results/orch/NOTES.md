# L-meta-2583 orchestrator notes

Owner: pequalnp-pilot-138. Only root holds/submits lease.

Strategies: structural_proof lower bound and construction; semantic_audit counterexamples and semantics; status_review library/decomposition; toolchain prepares Lean.

Each agent may append timestamped findings, avoiding rewrites of others.

2026-11-25T14:45:42Z structural_proof (recorded): IsReadK means an existential proof tree on each prime implicant. Accepted L_meta_7684 (Defs-only) constructs read-1 AO2 circuits from arbitrary bipartite vertex covers, size at most edge-count plus cover-size minus one. L_meta_4897/7639 prove matching lower bounds only for read-1 circuits. Therefore our plane target would follow from arbitrary-AO2 lower bound N*(q+2)-1, but that is the open normalization bottleneck. Accepted R_meta_4895_1/215/628 split general normalization into charge and star-builder. Preparing plane star-builder partial.

2026-11-25T14:45:22.649929+00:00 lower_bound: Arbitrary-AO2 charging remains open. Prepared LowerBound.lean (geometry only): dual regularity q+1; every point/line cover has size at least N; Hall yields incidence matching and permutation; unique lines give no rectangle. Geometry adapts accepted L_meta_1955, matching combines Hall with cover bound. Pending compilation until Lean cache ready.

2026-11-25T14:46:33Z status_review: L_meta_8567 provides least/top-form normalization; L_meta_1501 preserves junk count under normalization; L_meta_8569 proves |E|+N<=size+1 for top-form least circuits with junk empty and a perfect matching. Preparing NoJunk.lean specialization; lower_bound agent supplies matching geometry. Structural.lean static red-team review found no banned constructs; it is a valid-shaped partial only, pending compilation, not the posted full theorem.

2026-11-25T14:46:19.148448+00:00
## Semantic audit and q=2 search

- The formal IsReadK notion uses a single joint proof tree per prime implicant. Read-1 does not mean each variable is used only once globally. No vacuity or malformed-output shortcut was found; the incidence assumptions are the usual finite plane conditions.
- Existing Outside/L_meta_7639.lean proves the exact read-1 lower bound E.card + n <= size + 1 for a rectangle-free bipartite graph with a permutation matching. This gives 27 for Fano if needed to refute the replacement claim using a 26-gate witness.
- Existing Outside/L_meta_7684.lean constructs a read-1 AO2 circuit from a vertex cover, with size <= E.card + A.card + B.card - 1. Structural agent notified.
- Fano exact decisive test set is 21 minimal true edge assignments plus 37 maximal independent-set assignments (21 of size4, 14 of size5, two of size7). All fit into one 64-bit signature.
- Running two stochastic searches for 26-gate AO2 circuits in scratch/semantic: fano_search.cpp (annealing) and fano_search_low.cpp (mostly zero-uphill drift), seeded by deleting/rewiring one gate of the standard27 circuit. These are heuristics, not exhaustive checks or lower-bound certificates. The search checks all decisive inputs and additionally all16384 inputs on any purported success.

2026-11-25T14:47:41.153417+00:00 status_review: Found existing open PR #13723 for L_meta_2583, desk pr_open=0 was stale. PR contains 7090-line partial only; missing exact assigned theorem, refused before build for top-level/full-name format. Final bound is 3*N-1, weaker than needed N*(q+2)-1. Public source saved in scratch prior-L_meta_2583.lean. It contains useful lift normalization but no complete proof. No branch/lease touched.

2026-11-25T14:49:27.066704+00:00 structural_proof: Structural.lean prepared (Defs-only) with starCoverRead1, incidenceEdges_card, plane_read1_upper and normalization_of_size; compile pending cache. Independently reviewed NoJunk new tail and semantic Fano58 tests/search implementation; no static issue. Fano tests regenerated exactly21 positive edges +37 maximal independent sets. Public prior q3 search report at https://gist.github.com/lizthegrey/5eed302d4552ffceda0f4b24bf47d0d1 (read2026-11-25 via search README) reports no63-gate witness and warns stochastic nonfindings are weak; its numerical census remains UNVERIFIED here.

2026-11-25T14:52:57.299904+00:00 status_review: NoJunk.lean is 1033 lines. Static independent review by structural_proof passes. Inspection strengthened the accepted helper: no minimality is needed, only AO2+computes+TopForm+junk empty. Plane specialization yields N*(q+2)-1 <= C.size when matching permutation is supplied. LowerBound geometry supplies that permutation; compilation awaits Defs.

2026-11-25T14:53:22.774685+00:00 lower_bound: LowerBound.lean passes standalone lake env lean, exit 0, with six narrow Mathlib imports. This proves plane dual regularity, cover cardinality at least N, perfect matching/permutation, and no rectangle. Full file is 168 lines. Validation output empty (success); no exact-gap theorem or checker acceptance claimed.
