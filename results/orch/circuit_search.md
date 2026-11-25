Circuit search for L-meta-2592

Independent stochastic route, using full 1024-input truth tables in C++.

Started exact-coordinate optimization: for a chosen gate, evaluate the circuit suffix with that gate forced false and true, derive the gate care mask, and enumerate all AND/OR/NOT gates over preceding wires to pick the best replacement. Random tie-breaking, thermal noise, and restarts from vertex-cover20gate circuits with one gate removed. Invalid reads are represented by one freefalse source.

Program: /tmp/oec/pequalnp-pilot-103/circuit-search/coordinate.cpp. Logs: coordinate-1.stdout and coordinate-1.stderr. Counterexample agent retains independent SMT circuit synthesis and can locally repair candidates. No witness yet; optimization is not an exhaustive proof.

Ordinary coordinate-search paused on root request to free a CPU for Lean compilation. Bestscore18:18false negatives,0false positives,1unusedNOT; candidate saved as scratch best.json. Active-NOT variant continues, penalizing absence ofNOT in the outputcone.

2026-11-25T14:11:11.822942+00:00 ActiveNOT search best21false negatives,0false positives; no witness. Prepared elastic.cpp:24gate slots, preserve exactfunction with128-per-error score, minimize effective livegatecost (including requiredNOT). Root may run next after fixed19search.

2026-11-25T14:13:20.815262+00:00 Stopped fixed-19 active-NOT search at best21 false negatives, no false positives. Started 20-minute correctness-preserving elastic search (24 slots). Seed is exact Petersen function, cost21 means20 live monotone gates plus1 unusedNOT needed by target. Each accepted coordinate step keeps truth-table correctness because one mismatch costs128 while livegate cost plus noise is atmost37. Objective≤19 would be an actual counterexample after trimming deadgates.

2026-11-25T14:18:29.614425+00:00 Replaced elastic baseline run after no improvement with elastic_neg.cpp. Improvements: unbiased AND/OR/NOT sampling for dead helper gates; random swaps of independent adjacent gates; exact score-preservation checks for every permutation batch. One CPU, bounded20minutes. Old stdout/stderr preserved.

2026-11-25T14:20:37.610453+00:00 Added exact two-gate resubstitution using one dead helper and one live gate. All candidate expressions are tested on the live gate output care mask; each accepted move is checked against the full1024-input table. Source elastic_resub.cpp, logs elastic-resub-1.stdout/.stderr. One CPU,30-minute cap; interrupt handler preserves final iterationcount. No candidatebelow21 objective yet.

2026-11-25T14:22:32.750029+00:00 Search source checkpoints:
coordinate.cpp sha256=172344ea69f888a5350ebcadf57f08a8e5a8b2184c42593b3a2867d9185304dd
active.cpp sha256=921d6d6178d86c63c22be3f32c4d4f004036e875e7c8ce3d6e80e278de985704
elastic.cpp sha256=debe4fd9bcbfb56044c2b5683bf0e53b03445ba374503156f08232c3328c09c2
elastic_neg.cpp sha256=cee3390096c51362f21020f044225f98093989bcfb81922c8644cd337211dde4
elastic_resub.cpp sha256=c7fcc921492b63a8feaf22af90649c8bf0284213fb81e8e68760c86fda3897ea

2026-11-25T14:24:25.335360+00:00 Recompiled unchanged elastic_resub.cpp with supported -march=native to enable hardware population counts, and restarted with seed259207 for30minutes. Previous portable run ended normally: done 5461000 best 21. New logs elastic-resub-native.stdout/.stderr. Still one CPU.

2026-11-25T14:25:52.807697+00:00 With generic17-binary lower bound checked, redirected one CPU to nine-variable cofactor (delete Petersenvertex0). Native original run ended done 3547000 best 21. Cofactor baseline independently evaluated on all512 assignments:0 mismatches,16 live monotone gates. Searching for16 gates includingNOT; source cofactor_resub.cpp, logs cofactor-resub.stdout/.stderr,25-minute cap.

2026-11-25T14:36:52.309660+00:00 Cofactor elastic run stopped: done 49538000 best 17. Started free_phase.cpp, seed259209,25-minute cap. This searches15 binary gates with arbitrary complemented inputs/outputs; for an exact512-input circuit it enumerates32768 wire phases to minimize sharedNOT realizations. Any resulting ordinary size16 circuit will be independently validated before claiming a witness.

2026-11-25T14:40:06.776736+00:00 STOPPED immediately on root notification of lease HTTP410. All owned searches stopped; current free-phase run ended done 16723000 best 6 minnot 100. Complete program sources, JSON seeds and stdout/stderr are now preserved under results/orch/search/. No witness found; no exact15-binary-gate cofactor circuit found. Awaiting new lease before any further work.
