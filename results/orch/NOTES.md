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
