# L-meta-670 signed and slack-one native diagnostics

These computations are UNVERIFIED as Lean proofs. They do not establish the posted theorem or a checked binary-gate lower bound. The package preserves complete native outputs and source.

`live_signed.cpp` represents signals up to complement and permits all four signed AND variants for each pair. It uses cardinality and diagnostic-pair separation filters, exact state memoization, and removes constant/equal new gates. `signed12nosym.out` records a completed native exclusion at binary budget12 (807,139calls,27.2253s). `signed13nosym.out` is UNKNOWN after a40-second limit; it is not an exclusion. Compile with `g++ -O2 -std=c++17 live_signed.cpp -o live_signed`; run `./live_signed 40 10000000 13 0` to reproduce the capped b13 test. The b12 completed run used the same engine and budget argument12.

`live_signed_bounded.cpp` additionally stops at sampled RSS750,000KB. Commands for the recorded b14/b15 runs: `./live_signed_bounded 15 700000 14 0` and `./live_signed_bounded 15 700000 15 0`. Both returned UNKNOWN at720,896calls. Resource checks occur every65,536calls, so limits may overshoot.

`slack_one_counts.py` independently implements the multiset phase model in Python on414 diagnostic pairs. It begins with all9 raw phases plus each of154 possible first binary-output phases. One unit of slack permits either duplicating a signal freely once or retaining one binary operand; otherwise each binary merge consumes two signals. It checks coverage before entering the recursion. The phase convention complements the packed828-bit signal exactly when packed bit477 is set. Four signed AND operations are deduplicated; pairs are unordered. Both `python3 slack_one_counts.py memo` and `python3 slack_one_counts.py nomemo` exhaust all154 first signals at depth4 with no surviving path. This is a diagnostic of the proposed overapproximation, not a formal circuit-to-model soundness proof.

Memo mode resets its cache between each initial signal:77,781valid recursive calls,26,876unique valid states,4,559,466candidate trials. No-memo mode:185,820valid recursive calls,27,757,176candidate trials. The smallest no-memo initial case has727validcalls; the largest3,585. Full per-case counts are in the JSON files. `slack_one_counts_selected.py` additionally accepts a single initial signal index and streams each completed row to stderr.

## Extended b13 bounded probe

`live_signed_b13.cpp` uses the same search as `live_signed_bounded.cpp` with a sampled RSS threshold1,500,000KB. Command: `./live_signed_b13 120 100000000 13 0`. It returned UNKNOWN after48.08seconds and3,014,656calls. The RSS report was1,960,204KB: allocation/rehash between checks overshot the sampled threshold. Only6 first-step branches were entered, so this is not evidence of near completion. Complete stdout/stderr and build log are preserved.
