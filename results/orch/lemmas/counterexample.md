# Counterexample search for L-meta-2592

## Semantics checked

`Circuit.wires` evaluates gates sequentially; missing wire reads are false. `FanInTwo` restricts to AND, OR, NOT and at most two operands. NOT uses the first operand only. There is no identified semantic loophole.

## Exact elementary computation

For the posted fifteen Petersen edges, exhaustive enumeration of all 1024 vertex subsets finds minimum vertex cover size 6 and exactly five minimum covers. One cover is `{0,1,3,7,8,9}`. Assigning each edge to one endpoint in that cover yields star neighbor lists:

- 0: 1,4,5
- 1: 2,6
- 3: 2,4,8
- 7: 2,5,9
- 8: 5,6
- 9: 4,6

Computing each star and ORing the six star outputs costs `(15-6)+6+(6-1)=20` binary gates. This is an upper-bound construction, not a proof of the claimed lower bound.

## Stochastic searches

`counterexample_search.cpp` evaluates every proposed circuit on all 1024 assignments using 16 machine words per wire. It uses only two-input AND/OR and unary NOT, all references to earlier wires, exactly 19 gates, and at least one NOT. Mutations are neutral or improving hill-climbing with repeated restarts from deletion variants of the 20-gate construction. Occasionally the objective weights assignments of Hamming weight at most two more heavily.

Two initial bounded five-minute runs:

1. Seed2592, at least one NOT anywhere. Log `/tmp/oec/pequalnp-pilot-128/counterexample-search.log`; best circuit `/tmp/oec/pequalnp-pilot-128/counterexample-best.txt`.
2. Seed2593, requires a NOT reachable from the output. Log `/tmp/oec/pequalnp-pilot-128/counterexample-active-search.log`; best circuit `/tmp/oec/pequalnp-pilot-128/counterexample-active-best.txt`.

These are searches only. Failure to find a witness is not an exhaustive lower-bound certificate. No Lean-checked refutation exists from this work.


Initial seed2592 run finished: 290,497,211 proposals, 3,956 restarts, best10 errors; no witness. The best candidate was independently re-evaluated in Python, including its complete list of error assignments. Full completed log and candidate copied alongside these notes.

Third five-minute run uses seed2594 and randomizes all five minimum covers, edge orientation toward cover endpoints, star order, and OR parenthesization; it requires a reachable NOT.

Next fifteen-minute regimes preserve an exact NOT count in every mutation. Exactly-one-NOT additionally requires its input h to be true on at least one maximal independent set and false on at least one edge. Without those sign witnesses, monotonicity of h and the suffix permits replacing the NOT by constant true or false while preserving the target; the known monotone lower bound would then apply.

Verified independently: the target has76 false assignments and15 maximal independent sets, masks `[50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]`.

First exactly-one-NOT run (seed25921) was stopped because the filesystem filled at process start, leaving its stdout stream failed and logempty. Its saved best candidate has16errors and is preserved as counterexample-one-not-best.txt. It reached at least40,390,830 proposals, from the saved candidate record. This run is not a completed fifteen-minute result and should be repeated once space is available.


Stopped on root instruction after lease410 at14:40UTC. No stochastic process remains active. All existing logs and candidates copied into this directory. The one-NOT stdout log is empty because ENOSPC occurred at startup; its candidate is preserved. Active-NOT and randomized logs may lack their final summary lines because stdout failed while disk was full. All three original five-minute processes returned exit1 (no witness). Best observed errors: unrestricted10, reachableNOT15, randomized14.

The best10-error candidate computes a supergraph adding two unwanted edges, (3,6) and(2,9). Its offending biclique is node17=(x3∨x9)∧(x4∨x2∨x6). Node23 is unusedNOT. Generated topologically equivalent seeds placing that NOT at gate positions0,3,6; full1024-row Python evaluation confirms equivalence. All three shift offendingnode17 tonode18. These were prepared for SAT localrepair immediately before leaseSTOP; no new search ran afterSTOP.
