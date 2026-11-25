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

2026-11-25T14:55:04.780495+00:00
- Semantic search update: exact q2 decisive set and the C++ full-circuit search were independently audited by structural_proof. Added small-block search minimizing k - |accepted edges| + tau(remaining edges); <=5 yields a full26-gate candidate by completing a starcover. Structural_proof independently audited objective, SOS minimum-cover table, and seed rewiring. All seven known s-star baselines were independently checked at score6 in Python.
- General26-gate BV-Z3 and anchored OR(0,1)+colex BV-Z3 both returned UNKNOWN under configured180s and300s budgets. The original wrapper requested a model after UNKNOWN and therefore lost the detailed reason; timeout is inferred, not recorded. Fixed27-gate BV encoder check was SAT. Wrapper now records reason-unknown before any model request.
- Added pure-Boolean one-hot26-gate synthesis encoding, validated against fixed27 baseline (SAT, 1.338s). General26 search is ongoing with300s budget. Source and complete outputs are under /tmp/oec/pequalnp-pilot-138/semantic/.

2026-11-25T14:58:45.301280+00:00 structural_proof: Structural.lean compiled with exit0 using PEqualNP.Defs only.1190lines. Full compiler output preserved results/orch/structural-validation.txt. The upper bound and normalization_of_size conditional lemma are checked partials, not full gap proof. Independent static review by status_review passed. Parent notified to push immediately.

2026-11-25T14:58:48.543833+00:00 status_review: NoJunk.lean COMPILED exit0; 1033lines47668bytes; SHA256080d03e7f47695eb1176f6a07b6fa65fbc2fe0ee8f819af9e235b1d5c9a15272. Three deprecated-lemma warnings only. Full log scratch nojunk-build-01.log. Independent static review by structural_proof passed. This proves plane lower bound for top-form circuits with no junk, not arbitrary circuits.

2026-11-25T14:58:55.883998+00:00 lower_bound: FanoBlock.lean finite kernel decide completed successfully (exit0, empty output) just before planned cancellation. Proves five selected point/line vertices leaving six incidence edges have endpoint support seven or nine. Peak observed RSS3.7GB, ~4min walltime. No native_decide. This does not prove full gap.

## Root re-plan at 2026-11-25T15:01:34.059340+00:00

The unrestricted normalization is still missing: no-junk/top-form + construction + geometry now compile, but no proof eliminates dirty internal AND gates at unchanged size. Reductions are not enabled for this lease. Next work: (1) strengthen endpoint-support/read-once bridge and finish the small Fano block obstruction; (2) phase-guided finite SAT plus independent order3 search; (3) preserve/check conditional partials, with no proof PR unless the exact statement is proved. Six subagents total including the delegated read-once reviewer.

2026-11-25T15:01:54.491196+00:00 readonce_obstruction: ReadOnceSupport.lean (1019lines) compiled exit0. Adapted ReadTwoBridge+LeafBound, dropped unused Core conditions from leaf_bound: any belowF gate with an accepted readtwice pair has accepted-edge endpoint support bounded by cone gates. Parent structural_proof independently reviewing before rootpush. Mathematical pair-graph theorem also established: positive read-once formula rejecting singleton inputs has a disjoint union of complete bipartite pair components; C4-free forces stars. Together with finiteFano support lemmas this rules out all block-plus-star improvements using at most6blockgates on paper, not yet as a complete Lean theorem.

2026-11-25T15:03:17.555108+00:00 lower_bound: FanoSmall.lean passes (empty output, exit0): every Fano subgraph with at most six endpoints has at most six edges. Uses tiny degree3/common-neighbor finite checks and symbolic 3-by-3 counting. BlockSupport.lean passes (empty output, exit0): any essential input subset has cardinality at most circuit.size+1, hence the same bound for endpoint support of a computed bipartite edge function. Independent review requested for checkpoint pushes.

2026-11-25T15:03:17.895949+00:00 toolchain/PG3: Independently regenerated PG(2,3) as cyclic difference-set incidence {0,1,3,9}; verified 13 points,13 lines,52 edges, unique point-pair lines, and704 maximal independent sets. Exact decisive set is756 tests (52 positives +704 maximal negatives), MIS size census6:52,7:468,8:156,10:26,13:2. Semantic audit independently reviewed generator and63-gate search code. Running three 300s full-circuit heuristics (anneal, neutral drift, multi-gate), plus900s weighted full search and two900s block searches. A valid block with k gates accepting m edges and residual matching tau gives upper bound52+k-m+tau; target k-m+tau<=11. No witness as of this note. Failures are heuristic nonfindings, not UNSAT or lower bounds.

2026-11-25T15:03:36.660181+00:00 Semantic CNF milestone: unrestricted27 solved SAT in3.177s using phase hints only, then independent full16384-assignment model validation passed. structural_proof independently audited entire directCNFencoding. Rootrenewed15:02:27Z and authorized30min unrestricted26 phase-seeded run; running, noverdictyet. Stablecomplete sources/logs/audit retained in results/orch/search. Hardblocksearch finished600s,4.13Bmutations,bestscore7all6sizes; no26candidate.

2026-11-25T15:05:06.466357+00:00 structural_proof: Independently reviewed ReadOnceSupport.lean hypothesis weakening and pruning of unused Trees declarations. Clean747line version compiled exit0 and has no custom inductive, attributes, options or forbidden tokens. Parent notified for immediate partial push. Also independently audited semantic fano_cnf.py direct Boolean CNF encoding (selectors, muxes, operations, output tests, all-used constraints and seed phase bias); no issue.

2026-11-25T15:06:56.248326+00:00 Semantic STOP: rootreportedHTTP410. SentSIGTERM at15:06:24Z to CNF26longrun andsoft-blocksearch; bothexit143. NoCNF26verdict,nocounterexample. Finalcompleteprograms,rawSMT,stdout/stderrlogs,static-auditREADME,andterminationstatus retained in results/orch/search. Baseline-blockvariantcompiledbutneverrun. Allsemanticsearchworkstopped.
