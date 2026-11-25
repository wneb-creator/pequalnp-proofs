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
