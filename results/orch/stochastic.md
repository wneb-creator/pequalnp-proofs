Started 2026-11-25T14:34:42.117926+00:00

One nice19 C++ worker, seed1182592, planned1200seconds. All candidates evaluated on all1024 Boolean assignments; no sampling. Full Petersen graph objective uses19 gates, and alternating30second phases target H=Petersen minus vertex9 with16 gates plus an exposed wire OR(x4,x6); such a witness extends by3 gates to the full graph. Truth distance weights assignments of cardinality≤2 but still includes every assignment. Inputs/gates exactly follow library semantics, including forward references asfalse; gates are AND/OR/NOT only.

Seeds: all5 size6 vertex covers of Petersen and3 size5 covers of H, random star-edge assignment/OR order, full-circuit deletion, SAT-agent model cross-feeding. Search: random restarts, neutral mutation, simulated annealing, perturbations ofbest candidates. NOTcount0 ispenalized; >2 NOT penalized. A score0 therefore has1or2 NOT andexact functions. Smoke test ran540000 mutations; bestfull candidate22 errors. Its full truth distance independently matched a Python interpreter. No witness found in smoke.

Program and full logs: /tmp/oec/pequalnp-pilot-118/stochastic/search.cpp, compile.log, smoke.log, run-1200.log. Best candidates saved asbest-0.json/full andbest-1.json/H; WITNESS.json appears only onscore0.
