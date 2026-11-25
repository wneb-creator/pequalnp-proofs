# L-meta-4970 orchestration notes

Assigned 2026-11-25T15:48:51.075531+00:00

∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1

Only root calls desk or commits/pushes. Strategies append findings with their name; Lean experiments under /tmp/oec/pequalnp-pilot-157 or results/orch/lemmas. Final proof must use its own namespace and exact statement.

Allowed project imports: PEqualNP.Defs only (plus Mathlib). No other Outside imports unless already transitively available through Defs.

## status_review — library scan, 2026-11-25

- Updated CONTRIBUTING requires all helper declarations inside the module's own namespace, full target theorem last. Current script and join ownership now agree after upstream update (root verified redirect).
- No direct stronger checked theorem found. The only outside file referencing `TwoColour.tCount` is `L_meta_4791.lean`, which converts arbitrary AO2 circuits to T=0 with factor-six overhead, so cannot give the exact requested bound.
- `L_meta_4990.lean` is the closest complete result: the exact edge-count-plus-vertex-cover bound for C4-free incidence when every AND gate combines a right-pure OR closure with a left-pure OR closure. Its full theorem starts at line 937; it has 900+ lines of potentially reusable structural counting proof. Target hypotheses do not immediately imply its syntactic AND restriction.
- `L_meta_4897.lean` proves the same bound under `ReadK.IsReadK ... 1`; theorem at line 1929. `L_meta_7639.lean` specializes this to a perfect matching lower bound. Target hypotheses do not imply ReadK=1.
- `R_meta_3491_471.lean` proves the broad desired bound conditionally from a cofactor-size-reduction lemma and a smaller core lemma; it contains dependency-support and incidence-elimination infrastructure. `R_meta_3491_473.lean` offers another conditional recursive elimination route.
- `L_meta_7596.lean` bounds the sum of active left and right vertices by size+1 for general fan-in-two circuits computing true on all edges and false on singletons. This is too weak for dense edge sets but useful in matching/forest cases.

## semantic_bound preliminary

Closest existing full bounds require IsReadK1 (L_meta_2237/L_meta_4897), or no dirty AND accepting two distinct reread edges (L_meta_8933). tCount=0 alone gives every OR reach monochromatic, but does not prohibit dirty rectangle ANDs: (x1 OR x2) AND (y1 OR y2). A draft of the immediate no-two-colour and monochromatic-reach lemmas is in lemmas/SemanticNoMixed.lean, awaiting Lean setup.

### status_review — L4990 adaptation detail

The main count in `L_meta_4990.lean` partitions gates into LL (pure OR gates with at least two singleton supports), A (AND gates that OR-reach the output), and PU (OR merge gates above A). `leaf_count` at lines 116–200 gives a general union-DAG leaf bound. `lsum` at 631–651 uses C4-freeness to make the per-center LL sets disjoint. `core` at 737–760 combines these counts.

The adaptation bottleneck is structural: `Good` (453) includes `AH` (450), requiring every AND input to lie in a class `Q` closed through OR gates only (`QH`, 377). `star` (491) uses this to express pair evaluations as products of singleton supports. T=0 does not by itself imply this: nested ANDs and redundant AND branches inside a semantically pure OR witness are permitted. Thus copying L4990 wholesale requires substantial normalization/generalization; copying leaf_count/lsum alone may help another semantic route.

## counting_proof 2026-11-25T15:51:14.908238+00:00
The posted sketch needs a component correction: one degree-4 centre may be served by two disjoint pair ORs, so the witness OR count is only 2 while degree minus 1 is 3. Witness gates need not be used by the output. A proof must balance components with AND/output combining costs.
Drafted StarCentres.lean with C4-free uniqueness of either centre for a support set of size at least 2, semantic uniqueness of embedded pure OR leaf sets, and left-v-right semantic incompatibility. Awaiting toolchain for checks.

## counterexample strategy, initial checks

No semantic loophole identified: exact binary AO/backward model and gate-count size are enforced. T=0 is structural, not semantic: an identity AND x AND x hides a variable from OR-reach, so proofs must allow this at its extra gate cost. Star witnesses may be unused but are charged to size. Empty-edge and zero-input cases are harmless.

Exhaustive C++ search under /tmp/oec/pequalnp-pilot-157/counterexample_small.cpp enumerated T=0 AO circuits below the claimed bound for all C4-free graphs with no isolated-edge component in 1x2, 2x2, and 2x3. Results: 1/8/35 target graphs, at most 1/3/4 gates, 11/10041/1490485 states. No graph-function output below the bound, even without the star-witness condition. This is computational evidence, not a Lean proof.

## semantic_bound pure-OR normalization

Correction: tCount0 constrains syntactic orIn only; hidden identities x AND x can mask semantic singleton supports. Draft SemanticPureOr.lean proves an abstract normalization: if monotone functions f,g have conjunction exactly OR_Q, one operand is already OR_Q. Evaluate at the maximal assignment vanishing on Q, then use monotonicity and singleton acceptance. This handles a semantically pure-OR AND gate, but OR children need not themselves be pure-OR.

### counting_proof semantic extraction 2026-11-25T15:53:31.138014+00:00
For any pure OR_Q witness, consider the complement-Q assignment. A monotone wire is below OR_Q iff it is false there. At a false AND choose a false operand; at a false OR both operands remain false. This bypasses AND gates to extract a pure union network that retains every singleton accepted by the witness. Any retained OR merge with >=2 singleton support belongs to at most one graph centre by C4-freeness. Across all witnesses of one centre, count leaves minus overlap-components. Missing final ledger: the remaining circuit must pay components plus chosen minimum cover minus 1.

Counterexample-side normalization insight: for OR_Q witness evaluate the circuit at the maximal assignment vanishing on Q. At an AND gate false there, choose a false operand; that operand retains every singleton accepted by the AND. OR gates false there have both operands false. This can extract a union network for one witness, but choosing AND operands simultaneously for multiple centres is the obstacle. A semantically pure OR witness can have structural orIn size 1: (x1 AND x1) OR x2. The extra identity AND must be charged in any leaf ledger.

## Toolchain setup (2026-11-25T15:53:56.296786+00:00)
The saved environment had no Lean executable or .lake directory. Installed official Lean 4.36.0 Linux binary under `/tmp/oec/pequalnp-pilot-157/toolchain/lean-4.36.0-linux`. Source `/tmp/oec/pequalnp-pilot-157/toolchain-env.sh` before Lean/Lake/checker commands: it sets PATH and PEQUALNP_REAL_LAKE (needed by tools/bin/lake shim). `lake exe cache get` is downloading pinned Mathlib artifacts; full setup log is `/tmp/oec/pequalnp-pilot-157/cache-get.log`. No tracked setup files changed.

### status_review — independent partial review and projection obstruction

Source review of `StarCentres.lean` and `SemanticNoMixed.lean` found no mathematical issue or hidden statement weakening. These prove helpers only; the full edge-plus-cover budget is still absent. No forbidden syntax, quotes, extra axioms, or admissions observed. On assembly, put imports first and consolidate the helpers under one allowed module namespace. No build run during cache preparation.

The complement-leaf-set projection idea has an allocation obstruction: let u=a AND d, v=b AND e, w=u OR v. Both f=w OR (a OR b) and g=w OR (d OR e) are exact pure OR outputs on disjoint leaf sets. Projection at the complements of {a,b} and {d,e} selects different false children at u,v; the same OR gate w then branches into two leaves for both centers. All four leaves can lie on the same color side, so T=0 does not prevent this. Consequently C4-freeness alone does not make projected branching gates unique; further redundant-branch pruning or an accounting charge to AND overhead is necessary.

Toolchain agent: at 2026-11-25T15:54:54.814713+00:00, `lake exe cache get` completed successfully (exit 0), all 9,117 files downloaded and decompressed. Lean/Lake are ready.

## cofactor_route — preliminary

Checked prior lemmas L_meta_5371 and L_meta_5720 implement false-cofactor compression with strict gate saving for an essential variable. A false-only simplifier can plausibly preserve T=0 because it bypasses ORs only, but the ≥2-leaf star witness property can fail when support shrinks. Deleting left v can make multiple {v,a} witnesses degenerate at a single right centre b; C4-freeness ensures such newly bare edges have distinct left endpoints across different centres, i.e. a star forest, not necessarily a matching.

A reusable exact subcase proof for all edges sharing one centre has been extracted from checked R_meta_3491_473 into lemmas/CofactorStar.lean (pending local compilation). It proves |E|≤C.size from essential-input counting alone, without T=0/star hypotheses. Main cofactor route still needs a degree+1 gate drop or a stronger induction ledger.

### counting_proof checked helper 2026-11-25T15:55:55.243745+00:00
StarCentres.lean compiled successfully using pinned Lean 4.36.0 via lake env lean; no diagnostics. Frozen for root review/push. Its final lemma cover_card_of_star_witnesses gives a vertex cover of size at most number of distinct witness indices.

## counterexample separate operation count check 2026-11-25T15:56:28.920620+00:00

At cofactor_route request, tested the stronger separate claims OR-count >= |E|-1 and AND-count >= minimum vertex-cover size. All 35 eligible C4-free graph functions on 2x3, all T=0 AO circuits through 5 gates, 86,606,101 states: no violation, without imposing the star-witness condition. Source/log: /tmp/oec/pequalnp-pilot-157/counterexample_opcounts.cpp and .log. Pure computational evidence only.

Toolchain agent: initial `lake build PEqualNP.Defs` passed (exit 0, 5,147 jobs; no Mathlib source builds), and `lake build checklemma` passed (exit 0, 5 jobs). Full logs `/tmp/oec/pequalnp-pilot-157/build-defs.log` and `/tmp/oec/pequalnp-pilot-157/build-checklemma.log`. Scratch proofs/checker can run after sourcing the toolchain environment helper.

CofactorStar.lean compiled successfully (lake env lean, exit 0, empty output) at 2026-11-25T15:56:57.287057+00:00. It contains single_centre_size and single_centre_cover, 198 lines. It uses only Mathlib and PEqualNP.Defs; no forbidden text found.

## counterexample expanded finite search 2026-11-25T15:57:30.415690+00:00

2x4 exhaustive check completed: 136 C4-free graph targets with no isolated-edge component, up to 5 gates, 399,653,516 T=0 AO circuit states. No output computed a target graph function below |E|+tau-1, even before checking star witnesses. Source/log counterexample_2x4.cpp/.log under /tmp/oec/pequalnp-pilot-157. No concrete counterexample found; strategy exhausted small cases and semantic loopholes.

### status_review — useful existing semantic counting infrastructure

Inspected all 110 narrowed linear-sum candidate theorem statements (full extraction saved in scratch JSON). Best reusable proof is `L_meta_986.lean`: `cut` (119–175), `support` (177), `owned` (205), and `countOne` (210–258). It proves a single output's |S intersect P|-1 lower bound on gates whose original singleton support intersect P has size at least two and lies in S. A cut frontier has at most 1+owned-gates nodes; complement evaluation ensures every false frontier node supports at most one demanded singleton. Its constant-true exceptional wire z is for a one-NOT application and can be removed for the monotone case. This gives center-disjoint charging, but currently charges AND as well as OR gates.

`L_meta_1376.lean` supplies stronger versions: `smart_cut` at 294, `count_eq_R` at 595, `count_general` at 648, and `owned_disjoint` at 744. The first handles a separate excluded unary-gate set; it is more complex than needed here.

Counting agent's repaired projection is sound: retain demanded ORIGINAL singleton supports. A wire false at complement Q has singleton support contained in Q by monotonicity. At AND choose a complement-false child; its original support contains the parent's demands. At OR branch only nonempty demands. Every retained branching OR therefore has at least two original singleton supports in Q, allowing C4-free unique-center charging. My earlier redundant w gadget is pruned because its original singleton support is empty. An OR-only cut proof can traverse AND with no frontier-size increment and count OR expansions only.

Independent review: compiled CofactorStar, SemanticNoMixed, SemanticPureOr, DemandPruning all pass source correctness/format review as partial helper results. Frozen 136-line target-path helper file likewise passed partial-preservation review. None proves or claims the full posted theorem; no proof PR is appropriate yet.

## semantic_bound checked identity normalization

2026-11-25T15:59:28.508554+00:00 SemanticIdentity.lean compiles: hideInputs prepends one AND identity per input and shifts the original circuit. Its size is n+C.size; it preserves all evaluations and IsAO2 and has tCount=0 for every colouring. Thus tCount0 alone is a weak syntactic restriction. Combined with appended same-colour pair OR witnesses at each degree-d left centre, the target would imply for balanced d-regular C4-free graphs on N+N vertices: C.size >= N*floor(d/2)-N-1. This is a general Omega(E) monotone lower bound, substantial beyond the preliminary ledger. PureOr and NoMixed helper files also compile cleanly.

### status_review — compiled disjointness sum and new count review

Authored and Lean-checked `results/orch/lemmas/SumOwned.lean` (exit 0, empty diagnostics at scratch sum-owned-build.log). Its two generic lemmas establish center-disjoint owned support gates and sum |Q_i|-1 bounded by their common gate universe. Counting agent independently reviewed this file PASS.

Independently reviewed counting agent's 394-line `OrOnlyCount.lean` source PASS, including split_false, weighted frontier_cut, and count_or/count_or_one. The repaired bound is genuinely OR-only and supports multiple output roots F: S.card <= F.card + ownedOr(S).card, provided S singletons are covered by F and all F wires reject complement S. Latest compile verdict is counting agent's responsibility. The proof bypasses ANDs without increasing frontier cardinality and counts OR expansions only; terminal singleton supports cover S.

Reviewed `SemanticIdentity.lean` source PASS for partial preservation: n input-copy ANDs and global index shift preserve evaluation/AO2 and force syntactic T=0. Size is n+C.size, expressly not size-preserving. Reviewed the unified 475-line named helper module PASS for namespace/import assembly and clean diff.

### counting_proof OR-only count checked 2026-11-25T16:01:11.214274+00:00
OrOnlyCount.lean checked with pinned Lean (exit0, empty diagnostics), independently reviewed by status_review. Namespace PEqualNP.Outside.L_meta_4970.OrCount. Final count_or: for output frontier F, all false on complement S and covering every singleton in S, S.card <= F.card + ownedOr(C,S).card. ownedOr contains only real OR gates with original singleton support card>=2 and subset S. count_or_one yields |S|-1. The weighted frontier proof expands AND through a single false child at zero cost and OR through both false operands at cost1. This handles redundant branches correctly.
DemandPruning.lean also checked and independently reviewed: complement characterization, AND choice, singleton inclusion, disjoint demand splitting.

## counterexample multicycle exploration

Built anneal_graph.cpp under job tmp. Monotonicity gives a complete test set: positive edge pairs and negative maximal independent sets. Subdivision K4 needs 24 tests (12+12), Fano 58 (21+37), so all patterns fit one machine word. Canonical controls use (AND,OR)=(4,11) and (7,20) and have zero errors/T0. Four initial random-search runs of 30 million proposals each found no exact circuit: subK4 (3,15) best misses 3 edges; subK4 (8,10) misses1; Fano (6,24) misses3; Fano (11,19) misses1. Best cases reject all negative tests and have T0. These failures are heuristic evidence only, not exhaustive or Lean-checked. All complete stdout logs are anneal_*.log in job tmp.

## cofactor_route — AND-count route and literature, 2026-11-25T16:04:55.836267+00:00

The generic claim biclique-cover-number ≤ AND-count is false: primary Jukna TR05-021 explicitly gives a multiplicative gap. Read https://eccc.weizmann.ac.il/report/2005/021/download/ on 2026-11-25. Printed p.3 defines saturation by making each side a clique; Theorem3 uses saturated matching. Thus these examples are not bipartite or C4-free for large n. Theorem4 total-gate gap uses saturated Sylvester graphs (pp.4,12–13); its underlying bipartite graph only excludes K_{t,t} at t=O(log n), not K2,2. No C4-free gap follows.

Subdividing all old edges creates a bipartite C4-free incidence graph, but its function becomes OR_e y_e(x_u OR x_v), introducing independent y_e inputs. Transferring the cheap saturated circuit to this function is UNVERIFIED; no such reduction was found in the primary source. The C4-free/T0-specific AND-count ≥ minimum-cover claim remains unresolved.

## toolchain / independent mathematical sanity 2026-11-25T16:06:37.585154+00:00

Verified the identity-padding consequence precisely. For a balanced d-regular C4-free bipartite graph on N+N vertices, d>=2, |E|=Nd and every cover has at least N vertices by counting covered edges (each vertex covers at most d). Add input identity ANDs, then append ceil(d/2) same-colour two-leaf ORs at each left centre, pairing its d distinct neighbours and reusing the first neighbour for an odd leftover. These unused gates meet every exact star-witness quantifier and do not alter the output. With 2N input copies, theorem would force s >= N*floor(d/2)-N-1 for every original monotone circuit of size s.

Improvement: only one input colour must be masked, requiring N identity ANDs. Remap old left input wires to copies, leave right inputs unchanged, shift old gate wires by N. Original OR gates then never directly read a left input, so OR-reach can only contain right inputs; the appended right-pair ORs also remain monochromatic. This strengthens the implication to s >= N*floor(d/2)-1. The one-colour transform is a mathematical observation, not yet Lean-checked. The previously checked all-input transform suffices for Omega(E) when d grows. No flaw or easy contradiction was found in the precise hypothesis matching.

Primary literature read 2026-11-25: Stasys Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, arXiv:1406.3065v2 (2014), Remark 10, https://arxiv.org/html/1406.3065 . It distinguishes multi-output linear Boolean maps Ax from single-output bilinear f_A, stating an analogous sparse-matrix lower bound was not known for general Boolean circuits then; formula/tropical/multilinear bounds are different. Thus the padding consequence reaches a documented historical barrier. Current 2026 status is UNVERIFIED (no current primary source establishing it was found); this does not prove the posted statement false.

### cofactor_route finite AND-budget check 2026-11-25T16:06:46.748881+00:00

All 120 C4-free 3×3 bipartite graphs with a perfect matching require at least three AND gates even allowing unlimited OR gates (C++ exhaustive evidence, not Lean-checked). Each OR segment flattens to a subset of the six inputs and earlier AND outputs. Enumerated 1415 distinct first-AND functions and 11,682,240 second-AND operand pairs, checking outputs g2 and g1∨g2 on all 64 assignments; zero hits. Complete source/log: /tmp/oec/pequalnp-pilot-157/and_two_unlimited_or.cpp and .log.

### counting_proof family aggregation and pruning 2026-11-25T16:07:35.499116+00:00
StarFamilyCount.lean checked exit0 with empty diagnostics, reviewed by status_review. Adds pure_family_count (union of pure support outputs), ownedOr_disjoint, and sum_pure_family_count. The aggregate bound is sum of centre-union leaf counts <= sum of centre root counts + total OR count, provided centre-unions intersect pairwise in at most one input. This explicitly retains the root-count overhead. Its prefix duplicates OrOnlyCount; merge only the three additions.
RootDomination.lean checked exit0 with empty diagnostics: supports dominated by another root support can be removed, and finite induction gives an antichain of supports with exactly the same union. More general overlap-component reduction remains open. A promising potential is number of connected components of original-support family on the frontier: AND replacement can only merge components; OR replacement can split at most one component; singleton terminals give |S| components.

### status_review — global witness pruning

`RootDomination.lean` mathematical review passed; initial name `undominated_root_subfamily` violated the literal `_root_` ban and was reported for renaming before preservation.

Authored and Lean-checked `IrredundantFamily.lean`: a finite family has a subfamily with the same union in which every retained member has a private element belonging to no other retained member. Use this on global witness edge sets, not only per-center leaf sets. It removes a root covered jointly by several other roots, which pairwise support-antichain pruning misses. Build exit 0, empty scratch irredundant-family.log. Independent review requested from counting agent.

The precise overlap correction remains essential: write U_c for union of leaf sets at center c, r for total selected root count, and delta = sum_c |U_c| - |E|. Combining the owned OR bound with the desired conclusion requires residual >= r + cover_size - 1 - delta, unless root selection supplies an additional stronger property. Merely partitioning edges does not prove this circuit inequality; it only identifies the duplicate-count slack. Full residual budget is still unproved.

## semantic_bound P5 obstruction to naive residual ledger

This is NOT a refutation of L-meta-4970. Let left vertices a0,a1,a2, right b0,b1, and E={a0b0,a1b0,a1b1,a2b1}. Circuit u=a0 OR a1; v=a1 OR a2; s=b0 AND u; t=b1 AND v; output=s OR t; unused r=b0 OR b1. Size6 and T0. Choose three witness centres b0,b1,a1, with roots u,v,r and support sets {a0,a1},{a1,a2},{b0,b1}. They cover E; ownedOR=3, rootcount=3, tau=2, remaining gates=3, so remaining >= roots+tau-1 is false (3<4). Sum support-cardinalities is6 versus Ecard4. The posted full bound still holds: Ecard+tau=6<=size+1=7. A valid repaired route must choose an appropriate minimal family and/or retain overlap surplus delta=sum supportcards-Ecard. The candidate remaining >= roots+tau-1-delta is not yet proved; arbitrary duplicate roots also require pruning.

### Exact AND-budget search (cofactor_route, 2026-11-25T16:13:37+00:00)

T0 AO circuits can be normalized into k binary AND gates, each operand an OR subset of original inputs and earlier AND outputs. The selected original inputs of each operand must have one colour; previous AND outputs have empty OR-reach. Original inputs cannot occur in the final OR for a nonempty graph function. This is encoded in `/tmp/oec/pequalnp-pilot-157/and_sat.py`. Positive edge assignments plus maximal-independent negatives completely determine correctness for monotone circuits.

Cycle C12 (6+6 vertices, 12 edges, minimum cover 6): no circuit with five AND gates, arbitrarily many OR gates, and T0. CaDiCaL returned UNSAT, exit20, 8.31 seconds wall time, 73,788 conflicts, 115,072 decisions. CNF has1870 variables and7317 clauses; complete log is `/tmp/oec/pequalnp-pilot-157/cycle12-5and-t0.log`. This is computational evidence, not a Lean theorem. Fano6-AND search remains running; pinned canonical7-AND control is SAT.

## counterexample direct SAT 2026-11-25T16:17:13.089527+00:00

Full posted-hypothesis 14-gate subdivision-K4 search encoded in sat_full.py: 4,704 variables, 76,068 clauses, 91 complete/support test rows, 22 possible star supports. Binary backward gates, arbitrary output (unused star witnesses allowed), exact T0 via two reach flags, each edge covered by an OR gate true on its support singletons and false on support complement. Canonical 15-gate pinned control is SAT; separate decoder confirms all 1024 assignments, T0, all12 stars, C4-freeness, tau4. Two target runs: baseline and ordered (7,254 added clauses ordering independent adjacent gates by operation/operands; cofactor_route independently reviewed symmetry). Each capped30minutes. No target verdict yet.

Dual auxiliary OR searches (unlimited AND) were stopped without verdict to prioritize fullcounterexample search; complete logs remain sat_or_subK4_10.solver.log and sat_or_Fano_19.solver.log. Canonical dual controls pass full truth/T0/star checks.

### Fano AND-budget search continuation (2026-11-25T16:20:42+00:00)

The original six-AND T0 SAT instance timed out at 600.00 seconds with UNKNOWN, after 2,789,677 conflicts. This establishes neither existence nor impossibility. The ordered-only variant was interrupted to cap auxiliary solver use at one CPU process; its complete log remains saved.

A new run canonicalizes the first AND gate under all 168 colour-preserving Fano automorphisms, enumerated independently by checking all 7! point permutations against the seven incidence triples and deriving the line permutations. All 32,385 unordered nonempty monochromatic-operand pairs partition into 517 orbits; a first-gate representative from each orbit is permitted. Adjacent independent AND gates are additionally ordered lexicographically. Both transformations preserve a representative because graph automorphisms preserve semantics/T0 and independent adjacent gates can be swapped with later references remapped. The new CNF has 4,135 variables and 28,735 clauses; a seven-AND canonical control satisfies all added constraints. Source: `/tmp/oec/pequalnp-pilot-157/and_fano_symmetry.py`; full running log: `fano-6and-t0-automorphisms.log`.

### counting_proof component-strengthened ledger 2026-11-25T16:24:01.786222+00:00
ComponentGraph.lean checked and reviewed: auxiliary graph connects negative-wire singleton supports at cost <=1 edge per owned OR and zero per AND. Spanning-forest cardinality gives vertex count <= charged gates + family component count. CircuitComponents.lean checks the subtype-S instantiation: |S| <= ownedOR(C,S) + cc(root-support graph on S), explicitly accounting for isolated unused S vertices. CircuitComponentSum.lean checks aggregation across separated centre families.
StarSeparation.lean checked/reviewed gives pairwise intersection<=1 for embedded left/right centre leaf unions. StarWitnessFamilies.lean checked constructs actual Q_a/P_b and root sets from all witnesses in finite J: adjacency, edge coverage, complement negativity, and singleton coverage. StarEdgeCover.lean checked bounds E.card by sum of centre leaf counts. CircuitLedger.lean now compiling combines these with the exact owned-OR UNION cost, preserving output-OR joining budget.

## semantic_bound checked output-OR separation

2026-11-25T16:25:03.928187+00:00 OutputOrSeparation.lean compiles cleanly. It copies the necessary ordinary reach-up proofs from checked L_meta_2237 into our namespace and proves: (1) bipartite edge-function correctness rejects every singleton; (2) any gate with nonempty ORIGINAL semantic singleton support cannot lie in the output OR closure; (3) any finite set K of such gate wires is disjoint from the exact output OR-closure gate-wire set. Thus all ownedOR families are disjoint from output joining gates. This separation needs neither IsAO2 nor T0. It does not bound the number of output-frontier ANDs or cover nested AND contributions.

## counterexample next full search 2026-11-25T16:27:40.213383+00:00

Prepared full Fano26 SAT instance: 18,642 variables, 481,425 clauses, 200 rows, 56 possible star supports. Symmetry variant adds adjacent independent-gate ordering and all168 independently verified incidence automorphisms, reducing first-gate unordered input pairs105 to6 orbits. Pinned27-gate control satisfies both symmetries, solverSAT; decoded truth/T0/star checks pass. Ready to replace current subK4 slots only after their caps, as root directed.

Sole retained annealer upgraded to v5 with exact star coverage in fitness, using128 monotone test rows packed in two words. Canonical27-gate control has zero functional errors, T0, and all21 edges covered. Earlier best26-gate near miss was exactly Fano minus one edge, and that same edge lacked a star witness; no extra minterms.

### Certified Fano six-AND CNF UNSAT (2026-11-25T16:28:20+00:00)

The automorphism-canonicalized six-AND T0 CNF is UNSAT (exit20, 63.45 seconds; 763,987 conflicts). A second run emitted a binary LRAT certificate (exit20, 74.67 seconds). The local independently implemented Std LRAT computational checker accepted all 28,735 clauses and 1,417,154 proof actions, exit0. The certificate has 148,051,462 uncompressed bytes; SHA256 `051c45c757d3ec5bf1d1f2827eaecd65f0bdcacca1c723d0b7bf6f6764e64c01`. Its deterministic gzip is 74,012,541 bytes, and a decompression/hash roundtrip passed.

Artifacts are preserved in `results/orch/fano-and6/`: exact CNF, encoders, complete logs, positive and negative controls, verifier source, certificate, hashes and reproduction README. Counterexample agent independently source-audited normalization, edge/MIS tests, orbit coverage and adjacent ordering: PASS. This is a verified UNSAT propositional instance plus a source-reviewed informal encoding argument, NOT a Lean theorem about circuits or a proof of L-meta-4970.

[counting_proof 2026-11-25T16:28:37.135790+00:00] CircuitLedgerFull.lean and OutputBoundaryCount.lean both compiled exit0 with empty complete diagnostics. The full ledger preserves negative and positive witness semantics, E.card≤leafSum≤exactOwnedUnion.card+componentSum, ownedUnion.card≤C.size, and a checked arithmetic finish from residual+overlap. OutputBoundaryCount adapts existing L2237 output OR closure frontier count: real AND gates reached through OR from output are at most reached OR gates+1. Independent review requested. Withdrawn an informal antichain-CNF construction: it matched pairs but wrongly accepts all-left inputs, so it was not a counterexample to ANDcount≥cover.
