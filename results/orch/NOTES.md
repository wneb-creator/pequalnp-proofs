# L-meta-1031 orchestration notes

Lease holder: root only. Branch: pnp/pilot-54.
Posted statement and assignment: /tmp/oec/pequalnp-pilot-54/desk-response-001.json
Allowed project import: PEqualNP.Defs only; Mathlib allowed.
Proof target: lean/PEqualNP/Outside/L_meta_1031.lean.
Agents use separate scratch Lean files under results/orch/lemmas. Never edit the target without coordination.
Reduction slots reported: 3 live; reductions_open true. Need inspect existing reductions before choosing any cut.

- 2026-11-25T01:06:19.013345+00:00: counterexample_search: exact truth-table BFS on all labeled girth>=5 graphs with n=1..4 found minima equal to star-cover construction |E|+vc-1; 1,2,7,38 graph targets, no counterexamples. Script Counterexample.py; complete results/log under scratch. Edgeless n=0 case uses zero gates and out-of-range output n. Constants/unary/repeated-value gates normalize away in any minimum nonconstant positive circuit.

- 2026-11-25T01:06:45.360801+00:00 structure_proof: Existing R1031_2 route reduces to sound-AND normalization L1904, because L1906 cleanup and L1600 sound-star are proved. R1904_137 splits into singleton normalization, singleton budget, and cover builder; R1904_493 splits singleton normalization and pair-safe normalization. Prepared generic intersecting_edges_star helper in lemmas/Structure.lean; not yet compiled (toolchain installation pending).

## Reduction review 2026-11-25T01:06:58.937866+00:00
- Three existing reductions R_meta_1031_1/_2/_3 fill the per-step cap; a fourth cannot be submitted under user rules, although local checker does not enforce desk counts.
- R1031_1: useful least circuit + cost-decreasing exchange on disjoint owned edges. R1031_2: least circuit with all AND signals sound + cleanup; R1031_3: least circuit with star profile + cleanup of empty owners.
- R1031_2 second child is checked by L_meta_1906 (946 lines). L_meta_1600 proves sound AND ownership star on C4-free graphs. Missing sound least normalization is L-meta-1904 (R1904_137/_493 only).
- L_meta_2666 constructs a least positive circuit for every graph. L_meta_2668 gives every gate a pivotal graph edge under removal; does not itself show an AND owns an edge. R1772_773 already isolates repair of a first empty-owning AND as missing third child.
- L_meta_5355 constructs useful vertex-cover circuits at size at most |E|+|T|-1. Exact lower bound / normal form remains the central difficulty.

## prior_gap_check research, 2026-11-25 01:07 UTC

- L-meta-1035 already has its counterexample twin checked upstream: L_meta_1036.lean (5 inputs, 21 outputs, 23 gates versus >23 positive gates), merged PR https://github.com/open-goat/pequalnp-proofs/pull/2095 on 2026-11-23 19:59:07 UTC. GitHub canonical upstream is now open-goat; brilliant-hq API endpoint redirects there. Full 22-page open PR census (2200 PRs) contained no title matching L-meta-1035/1036.
- For L-meta-1031, no unconditional star-cover circuit optimality theorem was found. BicliqueBlockCost/SharedBlockCost explicitly define UPPER bounds only.
- L_meta_2656.lean:933 gives HasBlockCost G C.size for C4-free graphs under the extra hypothesis that EVERY AND gate is semantically below the graph function. R_meta_1900_1 isolates the remaining normalization claim as h2. This is the same obstruction as R_meta_1031_2, not an independent resolved route.
- L_meta_1490.lean:139 (also L_meta_1876.lean:139) contains the easy biclique_star lemma: complete adjacency between sides A and B in a C4-free graph forces A.card <= 1 or B.card <= 1. Its proof is 10 lines using Finset.one_lt_card. L_meta_1490:684 proves star facts for sound top gates and explicitly tracks unresolved junk AND gates.
- L_meta_1491:2496 provides conditional gate-count inequalities involving Ustar, junk, and centreless gates, not the unconditional |E|+tau-1 lower bound. L_meta_1528:3453 handles exactly one junk gate conditionally.
- Only PEqualNP.Defs is an allowed project import, so any helpers from these Outside files would need copied into the assigned file and checked under its namespace.

- 2026-11-25T01:08:21.886240+00:00: counterexample_search: SciPy/HiGHS exact integer model reports C5 cannot be computed with 6 positive binary gates (45.0s, status Infeasible). Star-cover construction uses 7 gates. Model uses all edge minterms and maximal independent sets; monotonicity makes these truth constraints sufficient. NOT Lean certified. Full log counterexample-c5-milp.log in scratch; model CounterexampleMilp.py. C6 7-gate search running (300s cap).

2026-11-25T01:08:51.890680+00:00

## Ownership/normalization investigation
- R_meta_1031_2 already proves that sound AND gates with nonempty ownership have star ownership on C4-free graphs. Its main difficulty is the two assumptions: existence of a sound least circuit and cleanup to nonempty ownership.
- L_meta_2666 proves existence of a least monotone circuit for every graph; L_meta_2668 proves every AND in a least circuit is essential on at least one edge, via eraseGate. Essential does not imply first-active ownership.
- L_meta_1501 normalizes least IsAO2 circuits to TopForm without changing size or dirty-gate count. Thus sound least circuits can plausibly be normalized to no AND ancestry, after which essentiality gives nonempty ownership. Main unresolved issue remains sound least existence.
- Read primary paper Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf on 2026-11-25. Its circuit separation uses saturated extensions (both bipartition parts made cliques), so does not refute the triangle/C4-free statement. Paper explicitly distinguishes total gate count, conjunctive complexity, and multi-output families. Do not infer our target is false from this result.
- Amano/Maruoka paper metadata located, but full paper could not be fetched through web tool (429 from IPSJ PDF). Any detailed counterexample structure from that paper is UNVERIFIED.

- 2026-11-25T01:09:36.947857+00:00 structure_proof: Structure.lean checked with pinned Lean via lake env lean (exit 0); only deprecated push_neg warnings. Proves general nonempty intersecting edge families of triangle-free graphs have a common vertex, and contraposition giving two disjoint edges. File frozen for root review and early partial push.

## Exchange strategy 2026-11-25T01:10:55.207238+00:00
- Exchange.lean compiled cleanly: 106 lines, lake env lean exit 0; log /tmp/oec/pequalnp-pilot-54/exchange-build.log.
- Explicit P4 circuit (a∨c)∧(b∨d)∧(b∨c), 5 gates, rewrites to b∧(a∨c)∨c∧d, 4 gates. The first AND owns disjoint edges ab,cd, and the top AND owns none. Simple bypass of either AND by an operand fails; minimality needs a multi-gate exchange.
- no_four_common_center/p4_or_sharing prove that a sound star reusing OR(a,c) has center b, OR(b,d) has center c, and OR(b,c) cannot have a center at all in girth>=5.
- sound_or_singleton_center strengthens this: for any monotone signal F, if (x_a∨x_c)∧F is globally sound and a-b-c is a path, singleton support of F lies in {b}. Remaining obstruction is reuse by unsound downstream ANDs or signals with no singleton support.

2026-11-25T01:12:40.455521+00:00

## One-junk elimination and odd cycles
- L_meta_3760 (10,039 lines) proves no exactly-one-junk-AND least circuit for bipartite C4-free graphs. Its bipartite hypothesis is materially used, not just for triangle exclusion.
- At lines 8433 and 8504-8516, two common-neighbor steps propagate equal colors and rule out qb~v. The associated edges form the possible 5-cycle v--um--zstar--c′--qb--v; noC3/noC4 alone allows it. The analogous issue occurs at 9010-9017. Triangle-only uses at 8939, 9534-9537 and 9958-9959 can be generalized.
- Checked OddCycle.lean proves the elementary common-neighbor triangle lemma and gives explicit C5 with no triangles/no 4-cycles where two such steps do not force nonadjacency. Lean4.36 exit0, no warnings. This is NOT a counterexample to the assigned gap.
- To extend L3760, handle these odd-cycle cover-swap cases with additional local circuit/budget analysis; replacing hbip by htri directly is unsound. Counterexample agent searching minimum C5 circuits with a dirty AND to test whether stronger all-minima elimination is false.

- 2026-11-25T01:12:44.087323+00:00: ExchangeBoundary.lean compiled cleanly; kernel finite check confirms P4 output cannot be produced by <=2 sound-AND extension gates when all three OR signals (a∨c),(b∨d),(b∨c) must be retained. Inputs encoded by 16-bit tables 43690,52428,61680,65280; OR tables 64250,65484,64764; target ab∨bc∨cd=63688. Constants 0 and 65535 also provided free. All OR gates allowed; each AND output required to satisfy value & ~target=0. The unnormalized circuit produces target with exactly2 extra ANDs. A sound replacement requires3 gates, so preserving arbitrary external uses blocks the local exchange.

- 2026-11-25T01:13:26.495865+00:00 structure_proof: Checked generalized finite-set essential-input bound from Support.lean using only legal imports, then graph specialization: every nonisolated vertex essential; degree(c) <= circuit size for any fan-in-two edge-function circuit. Checked conditional leastness at this degree bound. Full 247-line version is scratch starleast-next.lean, awaiting root snapshot coordination; construction agent making canonical star witness to combine into exact posted conclusion on all star graphs with isolates.

2026-11-25T01:16:26.230726+00:00

## OneJunk cover-cost implementation (check in progress)
- Source provenance: OneJunk.lean copies infrastructure from upstream lean/PEqualNP/Outside/L_meta_3760.lean (commit9c4fa2b), under PEqualNP.Outside.L_meta_1031.OneJunk. The old proof contradicts every one-junk minimum for bipartite C4-free graphs.
- New target is weaker and applies to triangle/C4-free graphs: a least AO2 circuit with exactly one junk AND admits a vertexcover T with |E|+|T|≤C.size+1. Combined with the star-cover construction, this gives a sound replacement no larger than C.
- The strict-improvement tails needing bipartiteness are pruned. All branches use the one-junk global budget, with charges pen+mix+2centreless+coneGates≥|Ustar|+extra-cover-vertices−1. Singletonstar cases need cg≥U−1 and mix+2cl≥1. Doublestar cases use cg bounds from both sides and triangle exclusion to distinguish mixing witnesses.
- The remaining gap for the assigned theorem is arbitrary many junk AND gates. No global telescope or valid boundary-preserving local replacement has been proved.

## First-junk and gate-count investigation 2026-11-25T01:17:03.335074+00:00
- FirstJunk.lean compiles: a TopForm circuit with nonempty junk has a least-index junk AND with no AND ancestor, without assuming there is only one junk gate. General cone bound proved from a short fold invariant. This gives pure-OR predecessors, but does not isolate arbitrary downstream dirty gates.
- Proposed separate #AND>=vertex-cover and #OR>=|E|-1 strategy is exactly existing reduction R_meta_612_7. #AND bound known up to target5 (L_meta_217); full small n6 (L_meta_950); numeric Petersen/Fano lower bounds also available.
- #OR>=|E|-1 is known for pseudoforests with no4cycle in L_meta_599 and L_meta_4837, requiring every induced subgraph edge count <=vertex count. L_meta_598 gives general weaker #OR>=nonisolated vertices-nontrivial components-1. L_meta_287 gives exact counts for forests.
- L_meta_1006 counterexample to C4free vertex-cover/AND bound uses triangles and weak maximal-independent-set boundary promise, not exact graph function; it does not refute the noC3/noC4 exact-function strategy.

## Star-cover construction and star forests (prior_gap_check)

- StarCover.lean now includes checked cover_and_formula, cover_flat, cover_no_and_ancestor, cover_owned_stars, single_star_data, and generic cover_data. The generic wrapper computes exactly the graph described by its owner lists, uses sum(neighbor-list lengths)+number-of-owners-1 gates, and every AND owns a nonempty star in the posted TransGen sense. No graph girth assumption is needed for this construction.
- Checked log: /tmp/oec/pequalnp-pilot-54/starcover-build-08.txt (exit 0).
- StarForest.lean is a standalone checked snapshot combining StarCover and StarLeast. star_forest_minimal proves leastness when the flattened center-and-neighbor lists have no repeats (disjoint union of nonempty stars, with arbitrary isolated vertices). Log: /tmp/oec/pequalnp-pilot-54/starforest-build-01.txt (exit 0).
- Further library search found L_meta_3525 (1730 lines) already proves |E|+tau-1 circuit lower bounds for all acyclic graphs, and L_meta_5355 (401 lines) constructs a circuit from any vertex cover with size <= |E|+|T|-1 and nonempty ownership. Its N / edge_N / sumN_le helpers can instantiate our generic cover_data with explicit star ownership. General girth>=5 lower bound remains the missing piece.

- 2026-11-25T01:17:54.236498+00:00: ownership_lemma: OneJunk.lean checked successfully, Lean4.36 exit0. one_junk_cover_cost proves |E|+|T|≤C.size+1 for a vertex cover T when C is least AO2, graph has no triangles/C4, and junk.card=1. Frozen SHA256 b2ff037bc1ce38c4e6b6694e2b7593c03bce3e0eb143c264586f810f2b3512f1. This is a partial theorem, not L-meta-1031.

- 2026-11-25T01:18:35.609025+00:00: counterexample_search: C5 with7gates and any unsafe AND is solver-INFEASIBLE (HiGHS242.7s after cycle symmetry); C5 with8gates+unsafe is SAT(7.4s). All291 five-vertex forests exhaustively have minimum star cost and no unsafe minimum circuits. Combined covers all303 labeled girth>=5 graphs on5vertices (solver trust needed for C5). Lean-checked explicit8gate C5 boundary lacks star profile and has an empty AND owner; explicit7gate correct witness proves this8gate circuit is not least, so it is NOT a refutation of L1031.

- 2026-11-25T01:21:06.660716+00:00 structure_proof: Independent OneJunk audit passed (exact first8035 lines match L3760 modulo namespace; new weak budget/five branch endpoints checked; full recompile exit0). Main type uses intended TopForm.NoFourCycle/IsLeastAO/junk with triangle-free assumption and exactly one junk AND, and axioms only propext, Classical.choice, Quot.sound. Note IsLeastAO is normalized read-back/exact-fanin2 model, not public Monotone2. 477463bytes leaves insufficient room for current target helpers when concatenated unpruned.

- 2026-11-25T01:21:06.660733+00:00 structure_proof: Direct ownership exchange remains weaker than all-AND soundness. Possible inductive route narrows an operand of a star-owning dirty AND to its center literal when that center belongs to the operand singleton support, then prunes opposite OR support to graph neighbors; prior already-sound ancestors could be lifted to restore lost edge behavior. The overlapping-side/center-not-in-singleton-support cases and shared OR rewiring cost remain unproved. For nonstar ownership, lowering g loses edges with no earlier active AND ancestor, requiring redistribution to downstream filtering gates; this is the actual exchange difficulty.

- 2026-11-25T01:23:04.593616+00:00: direct_ownership: checked DirectOwnership.lean. Semantic edge-sandwich lemma allows narrowing an intermediate signal when all graph-edge valuations are retained. A pure-OR AND with nonempty activated-edge star and center c in an operand support can replace that operand by literal x_c at no added gate, preserving a monotone downstream context computing the graph function. If center lies in neither support, the graph has a leaf; minimum-degree>=2 eliminates that obstruction. This controls all activated edges, not only owned edges with earlier active AND ancestors, so it does not prove the full gap.


## Two-junk obstruction 2026-11-25T01:24:29.313086+00:00
- TwoJunk.lean compiled with Lean4.36 exit0. Generic rectangle_exhausted / rectangle_edge_function show that a full row and column in a C4-free bipartite rectangle exhaust all graph edges in that rectangle.
- Checked P4 circuit g=(x0∨x2)∧(x1∨x3), T=g∧(x0∨x3), output=(g∧x1)∨(T∧x2) has exactly2 junk ANDs, is TopForm, and every gate is pivotal on a graph edge under zeroing. Nevertheless g has2 direct readers, disproving any inference of the L5391 single-reader condition from those weaker properties alone. It is NOT minimum (8gates vs explicit4gate correct witness), so this is not a refutation of L1031.
- L5391 ignores all graph-girth, bipartite and pure-OR-support hypotheses in its proof; active exchange assumptions are LiftFixed/no-belowF-inputs, exclusive g→T reader, sound literal downstream readers, and deletion-count budget. Minimality beyond gate-essentiality is required to obtain those structures.

- 2026-11-25T01:33:32.041506+00:00: Independent numerical review completed in SEARCH_REVIEW.txt. No blocking model errors found. Verified BFS flag merging and graph symmetries; independently re-evaluated both MILP C5 witnesses on all32 inputs, including unsafe gate2 at mask20 for eight-gate witness. All MILP infeasibility remains solver-trusted research evidence, not Lean certificates. Source-version/argv provenance is incomplete for historical unsymmetrized runs. Theta/Petersen searches and C6 unsafe search are timeouts/no-witness only.


## One-junk public-profile connection 2026-11-25T01:36:03.770604+00:00
- OneJunkProfile.lean compiled on its first complete check, Lean4.36 exit0; full log /tmp/oec/pequalnp-pilot-54/onejunk-profile-lean.log. 519908bytes, 10255lines, SHA256 4609343866a0fd181e94a8a388afd692a21e7cc3b26f8a3cd134dbaeeb1d6d91.
- profile_of_one_junk has the exact posted existential conclusion, assuming an existing globally least public monotone fanin≤2 circuit C that is also IsAO2 and has junk.card=1. The wrapper converts graph hypotheses, obtains the OneJunk vertex-cover budget, invokes generic StarCover.vertex_cover_upper, and transfers minimum size back to the public model.
- Source copies frozen OneJunk and StarCover under OneJunkProfile subnamespaces. To fit512KiB, only unused lam_same_color, pen_zero_swap_bound, and bip_eq_of_common_nbr declarations were removed from the copied OneJunk infrastructure. Frozen originals unchanged. This is still a conditional partial theorem, not the unconditional L1031 gap.

## Cofactor substitution, 2026-11-25T01:36:09.276776+00:00
- FreshCore.lean semantic checkpoint builds cleanly with the pinned Lean (445 lines, SHA256 5d0ad7449fc6a75b16bedd68b598708bf45f60a967e477767a019493beda370e, full log freshcore-build-03.log). For arbitrary monotone context K, substitutable monotone signals are exactly the interval between the graph function of edges rejected by K(_,false) and the predicate excluding independent forced-true extensions. Exact decomposition: graphFun = K(_,false) OR graphFun(pivotal edges). This preserves all downstream sharing semantically; it gives no gate-realization cost for the canonical members of the interval.
- In a triangle-free graph, an AND of pure ORs with disjoint supports and at least one pivotal edge is either indispensable on two disjoint graph edges or can replace one operand by a literal center and compute the same graph function, retaining its other operand and all shared readers. The proof needs only a monotone full context; a separate concrete circuit bridge is in preparation. With overlapping supports and center outside both supports, dropping to the OR of their intersection works semantically but may cost additional OR gates.
- At an independent input I where forcing the selected AND true would accept, the undominated vertices from its two operand supports form a complete biclique, so one side is subsingleton under noC4. Bypassing via a single operand, whenever incorrect, admits a certificate I hitting that operand, missing the other and dominating every vertex in the other. Conversely, arbitrary subsets of activated graph edges can be pivotal and arbitrary feasible independent forced-true profiles selected using a monotone context, as proved by realize_exact, realize_pivotal and realize_negative. This identifies the need for a gate count or real-circuit structural argument.

- 2026-11-25T01:37:34.828456+00:00: FreshCore independent review PASS for partial scope at SHA5d0ad7449fc6a75b16bedd68b598708bf45f60a967e477767a019493beda370e. Reviewed all445 lines; recompiled and checked key declaration axioms (only standard three). No circuit-size/minimality assertion; semantic-context bridge only. See FRESHCORE_REVIEW.txt.

- 2026-11-25T01:38:33.139966+00:00: Independent CounterexampleOrMilp review PASS at SHA1bf2efa1815417b8f96046ca4b4db0d14b156d3939980a439ddaa1d8ecdd5f18. Model complete for <=k OR gates with unrestricted AND closure; checked local constraints by exhaustive Boolean enumeration. Default edge/maxindependent samples exact; pair-only SAT is relaxed evidence only. No solver run launched. Details appended to SEARCH_REVIEW.txt.
