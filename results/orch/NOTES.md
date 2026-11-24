# L-meta-1768 shared research notes

Only root holds and renews the lease. Read gap.json and repository instructions first. Each strategy owns its own file under lemmas; report findings to root for inclusion here.

Goal: count top-side/junk-OR-reachable pairs in Ustar, bounded by a universal constant times circuit size plus one. Full proof preferred; reductions allowed after at least 20 minutes of real effort.

## 21:50 UTC findings
- Existing R_meta_1768_1 already splits exposed junk witnesses (27 times size) and residual nested junk. Avoid duplicating it.
- L_meta_1876 proves junk empty implies Ustar empty. L_meta_1878 (952 lines) proves a one-junk bound with constant 12; its trace relies on the unique junk gate.
- A target endpoint is in wmax of its junk gate; L_meta_1878 has reusable semantic argument. R_meta_1880_311 contains topContact and contactBound for junk antichains.
- Setup claim was inaccurate: no Lean/elan or warm cache is present. Toolchain agent installing pinned 4.36.0 into scratch; only 7 GiB free may constrain cache.
- Lease renewed 21:49:55Z; expiry 22:09:54Z. Root alone handles renewals.

## Target-specific core reduction under development
- direct_bound is implementing results/orch/lemmas/reduction_core.lean, theorem R_meta_1768_45.
- Hypothesis 1: essential support of graph has cardinality at most circuit size plus one (known independent result). existing_results will extract a checked proof.
- Hypothesis 2: selected-edge subgraphs with no degree1/2 vertices satisfy a universal linear edge bound.
- Peeling low-degree vertices pays at most2 per supported input, leaving a minimum-degree3 core. Borrow generic proof from R_meta_1735_5; no duplicate of prior exposed/residual split.
- reduction_design independently checks smaller hypotheses and plausibility.
- counterexample exhaustive finite cases through4 vertices found no junk in any least circuits; Python evidence only.

## Candidate prepared at21:52Z
- Final candidate lean/PEqualNP/Outside/R_meta_1768_45.lean (98 lines) is the target-specific3-core reduction. Source/import/namespace guard passes. Build and checker pending toolchain/cache.
- Essential-input premise already checked verbatim in L_meta_2074; extracted support_bound.lean has222 lines and stronger fan-in-only local lemma.
- Exhaustive peeling validation on all32768 six-vertex labeled graphs passed; Petersen remains a genuine core test with15 edges.
- No submission before22:08:40Z (20min real effort). Direct agent continues investigating whether core can be eliminated/bounded directly.

## Independent direct-proof conclusion
Singleton restriction at anchor u propagates neighbors through ORs and AND gates whose other operand is true at singleton u. Girth prevents two anchors sharing multiple neighbors but does not bound how their selected propagation paths differ. The missing global accounting is exactly the part retained by the3-core premise. Formula lower bounds do not imply this unrestricted-circuit result.

The reduction has passed independent source review by repository_review and reduction_design. Final exact conclusion confirmed against gap.json. No Lean build or checker success is claimed yet.

Delivery archive plan: preserve notes, experiments and complete validation outputs in an early commit on pnp/pilot-45, then remove results from the final PR tree. The PR diff will add exactly the reduction Lean file, while earlier branch commits keep all results accessible.
