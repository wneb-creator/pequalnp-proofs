L-meta-2590 monotone Petersen search

Target: an AND/OR circuit of at most 19 gates; known baseline 20. The exact monotone specification consists of 15 minimal positive assignments and 15 maximal negative assignments. Any candidate is independently checked on all 1,024 assignments.

Root alone manages lease and git. Counterexample agent owns independent full-gate SAT/CNF searches; status_check owns the compact AND/free-OR and OR/free-AND macro encodings.

2026-11-25 15:13 UTC: after root confirmed renewal, started a fixed 19-gate stochastic search. Source search_petersen.cpp; complete diagnostics fixed19.stdout and fixed19.stderr. Stopped cleanly at approximately 15:20 UTC after 280,262,000 coordinate updates. Best score 1: one missing edge assignment, no false positives. No counterexample found. This is empirical search, not a lower-bound proof.

2026-11-25 15:20 UTC: with root authorization, switched the single stochastic CPU to an auxiliary OR-count experiment. Source search_petersen_or.cpp uses 32 available AND/OR gates, charges only live OR gates, and preserves the exact 30-row specification. Target is an exact circuit using at most 13 OR gates, with no AND-count restriction. The run is capped at 1,200 seconds; complete diagnostics or13.stdout and or13.stderr. Initial baseline was independently checked on all 1,024 assignments: zero errors, 20 live gates, 14 OR gates (or-baseline-validation.json).

The AND-count route is already known: status_check found L_meta_635 proving at least 6 AND gates. A circuit with at most 13 OR gates would challenge the complementary OR-count strategy even if its total gate count exceeds 19. No such circuit has been found yet.

2026-11-25 15:21 UTC result: the OR-count search found an exact circuit with 24 gates, comprising 13 OR and 11 AND gates, after 802,812 coordinate updates. It exited successfully. Removing an AND(8,8) copy yields 23 gates: 13 OR and 10 AND. Both the original and simplified circuits independently passed all 1,024 assignments. Files: or13-witness.json, or13-validation.json, or13-simplified.json, or13-simplified-validation.json. Thus an unconditional Petersen OR-count lower bound of 14 is false. This does not refute the posted total-size lower bound.

A total-size optimizer was then prepared in search_petersen_nonlinear.cpp and successfully compiled. It starts from the nonlinear 23-gate witness, gives precedence to smaller total gate count, and uses OR count as a tie breaker. A zero-second baseline run completed; the long search was never started.

2026-11-25 15:23 UTC STOP: root reported lease HTTP 410 at 15:22:00. No owned search processes were running at this point, and no new searches were started. All sources, complete stdout/stderr, candidate JSON files, and independent validation reports are present in this directory. No further work is authorized without a new lease.

Unverified algebra note identified immediately before STOP: in the simplified witness, gate 16 is AND(gate 15,input 3), gate 15 is AND(wire 17,wire 14), and wire 14 is OR(input 7,input 1,input 3). Replacing gate 16 by AND(wire 17,input 3) would make gate 15 dead and should reduce the circuit to 22 gates (13 OR, 9 AND). This change has not been written or independently checked because work stopped on lease loss.
