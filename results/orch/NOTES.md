# L-meta-2685 orchestration notes

Assignment: 2026-11-25 02:17:00 UTC. Only root holds and renews the lease.
Exact statement: `/tmp/oec/pequalnp-pilot-58/assigned-gap.json`, gap field.
Goal: size-preserving two-level normalization of AO2 circuits for C4-free bipartite incidence functions.

Strategies:
- library route: existing accepted reductions and reusable definitions/lemmas.
- normalization route: structural transformations of mixed circuits.
- counterexample route: finite cases and semantic edge cases.
- counting route: lower bound and explicit star-cover construction.
- root: coordinate, formalize strongest route, lease/build/check/submit.

Constraints: only PEqualNP.Defs project import; target one file `lean/PEqualNP/Outside/L_meta_2685.lean`. Three reductions are already live, the posted maximum. No further reduction unless capacity is confirmed. Environment setup in progress, no Mathlib source builds.

Append dated findings below. Each agent owns its named attempt under `results/orch/lemmas/`; coordinate all changes to final file with root.
2026-11-25T02:18:54.779456+00:00
## Library route (prior_refutation_status)
- Accepted reductions R_meta_2685_1, R_meta_2685_863, R_meta_2685_41 exhaust the three slots. 863 cuts ownership budget / coverCircuitB correctness / shape. 41 cuts exact lower bound |E|+matching ≤ size+1 / star compiler, proving Konig internally.
- L_meta_4181 (1474 lines): monotone circuit → least AO2 TopForm circuit of no greater size. L_meta_4543 (1150 lines): same with Ustar minimal among least TopForm circuits.
- L_meta_1491 (2507 lines): |E|+|tops\centreless|+2|centreless|+|junk|+|orN\lam| ≤ size+|Ustar|+1; minimum vertex cover of E\Ustar ≤ |tops\centreless|.
- L_meta_3760 (10039 lines): least C4-free bipartite circuit has junk count ≠1. L_meta_1876 says zero junk implies Ustar empty. Hence missing full-normalization content starts at ≥2 junk.
- L_meta_5391 is narrow two-junk-chain surgery; L_meta_5403 proves shared-operand rigidity from no C4. These do not imply the unrestricted target.
- Only PEqualNP.Defs permitted: Outside lemmas need copied/ported within own namespace, no direct Outside imports.

2026-11-25T02:19:59.292004+00:00 counterexample route: IsAO2 has ReadsBack and exactly 2 operands; no invalid-gate loophole. Invalid output is allowed and supplies zero-cost false, so empty incidence can use empty D/P/L. SAT synthesis for C6 found 8 gates; decoded circuit independently checked on all 64 assignments. Checking 7-gate C6 and 10-gate C8 now.

2026-11-25T02:20:03.219846+00:00 LibraryRoute baseline compiled with exit 0 using only PEqualNP.Defs; 1473 lines at results/orch/lemmas/library-route.lean. Log /tmp/oec/pequalnp-pilot-58/library-route-build.log. Exported lemma PEqualNP.Outside.L_meta_2685.LibraryRoute.leastTopForm. All helpers are lemmas.
Remaining surgery coverage: 3653/4712/4741–4747 assume one junk; 3760 eliminates one junk. 5391 handles a restricted two-junk chain with unique lower reader, singleton external filters, and private removable OR ancestors. 5138 handles a prescribed two-junk 2×2-support fork with private operand wires and private edges. General sharing/branching and >=3 junk remain unproved.

2026-11-25T02:20:14.916095+00:00
## Normalization route
- A monotone AND below a linear OR must have one operand below that OR: join two assignments missing all selected inputs to contradict containment. Proof drafted as and_below_linear in normalization-route.lean, awaiting cache readiness.
- This removes ANDs for a single linear target by tracing from its output. Applied to a point cofactor, target is OR of neighbors. Main unresolved step is compatible choices across cofactors/shared gates. An OR can serve different point cofactors via conditional children, so naive unique charging fails.

2026-11-25T02:20:34.765552+00:00 counting route: existing R_meta_2685_41 uses sharp lower bound |E|+|matching|≤size+1 and star realization, with matching-cover duality already proved inside the reduction. R_meta_2685_863 uses ownership-charge, coverCircuitB semantics/size, and shape. Compiled useful partial at results/orch/lemmas/counting-route.lean: coverCircuitB_isAO2 for bounded owners/input lists, establishing backwards-read validity plus exact binary AND/OR gate shape. Exit0, full diagnostics /tmp/oec/pequalnp-pilot-58/counting-route-build.log. Next candidate is constructing the pure-side P/L witnesses for canonical cover circuits.

2026-11-25T02:21:07.507721+00:00 counterexample route: C6 exact synthesis UNSAT at7 gates in5.6s, SAT at8 with separately verified64-row truth table; path on6 vertices UNSAT at6 gates (predicted optimum7). CNF generator and complete logs scratch synth-small.py and synth-*. No counterexample found. Empty-incidence Lean branch drafted in results/orch/lemmas/counterexample-route.lean, awaiting build readiness.

2026-11-25T02:22:20.327551+00:00 counterexample route: empty_incidence exact-conclusion partial compiled via lake env lean with exit0; 21-line results/orch/lemmas/counterexample-route.lean. Log counterexample-route-build.log is empty (success). Root notified immediately for partial push.

2026-11-25T02:23:26.134369+00:00 counting route: full constructive shape component now compiled. Lemma coverCircuitB_twoLevel in results/orch/lemmas/counting-route.lean proves IsAO2 plus exactly the requested P/L pure OR closure and mixed AND operand clauses for every oppositely tagged owner list. Does not need nonempty owner lists. It discharges all of R_meta_2685_863 shaped child; hard ownership-charge budget remains. Supporting new composition argument uses closed/shaped certificates joined by P/L unions and shifting gate indices. `lake env lean` exit0, /tmp/oec/pequalnp-pilot-58/counting-shape-build.log.

2026-11-25T02:25:01.670495+00:00 LibraryRoute AO2 simplification compiled: 1149 lines / 50373 bytes, down 324 lines. Exported leastTopFormAO directly takes IsAO2. Build log /tmp/oec/pequalnp-pilot-58/library-route-build-ao.log exit0.
Multioutput route: row neighborhoods intersect pairwise in at most one. An OR-only circuit for their ORs has cost at least sum(row cardinality minus 1), since every nontrivial OR gate can lie in at most one output cone. Normalization agent has derived last-AND elimination for a joint linear family, matching Nechiporuk historical theorem. Bilinear-to-joint-row extraction remains separate: one-hot point cofactors are row-dependent copies of each original gate; no aggregate size bound follows from ordinary cofactoring. Union/intersection matrix semantics loses false multi-input/same-side assignments and is not sound for full incidence function.
