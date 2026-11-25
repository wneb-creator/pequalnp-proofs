# L-meta-2585 computational searches

These artifacts are research evidence, not Lean proofs of negative search results.
Every candidate must still be independently evaluated and Lean-checked.

- `small_search.cpp` enumerates semantic circuits. Complete scans cover all333 nonempty3x3 C4-free targets through6gates. The six targets needing an8gate read1 star circuit are C6 up to the recorded permutations; its7gate SAT instance is UNSAT. Thus no smaller-than-star circuit occurs for3x3. The enormous generic7gate enumeration was stopped and did not complete.
- `validate_search.py` compares pruned/unpruned small enumerations and checks exact truth tables plus squarefree polynomials of all333 explicit star circuits.
- `synthesis.py` searches fixed gate counts using every edge assignment and every maximal independent assignment. This test basis is complete for monotone circuits. Adjacent independent-gate symmetry and verified graph automorphisms reduce equivalent candidates. Fixed-count UNSAT alone does not exclude all smaller counts.
- `synthesis_semantic.py` optionally requires incomparable input signatures and each gate accepting an edge. These restrictions hold for minimum circuits. Known star positive controls remain SAT.
- `point_read_one_search.cpp` checks an intermediate OR-count bound on point-once/line-positive proof monomials in both orientations. Its complete6gate scan checks2,036,784,434 canonical size6 circuits, finding no violation. The64 abstract multiplication states are independently checked.
- `or_count_search.cpp` checks the unrestricted edge-count<=OR-count+1 conjecture through5gates. The separate C6 eight- and nine-gate/at-most4OR SAT instances are UNSAT, each with a fixed same-size/5OR SAT control.
- Stochastic and time-limited SAT negatives mean UNKNOWN. K4-subdivision and Fano searches were retired after accepted full lower bounds were found upstream. Current larger targets are K5 subdivision23gates and cyclic8x8 offsets0,1,3 with30gates. PG(2,3)63gate annealing was retired after public discussion12644 revealed a much larger duplicate unsuccessful search; no lower-bound inference is made.
- Dynamic graph search retains full monotone antichain tests and checks any hit on all65536 inputs. The initial variant was retired after a smoke test of its slack variant revealed sparse-graph drift; the original run did not record density. The dense variant has40 slots, nine initially dead gates, at least20 output edges, and charges only the live output cone.

Complete logs are retained; `SHA256.json` identifies archived bytes. See adjacent `NOTES.md` for timestamped outcomes and limitations.

`decode_solution.py` independently checks SAT clauses and all Boolean assignments for any candidate, prunes dead gates, computes maximum matching, and identifies missing squarefree edge witnesses. It passed known C6 and K5 star controls. `SEARCH-BUILD.json` preserves dense-search compile flags and hashes; assertions must remain enabled.

Exact principal invocations, from the named job scratch directory (with `cadical` resolved to the installed Lean toolchain binary):

```sh
python3 synthesis.py k5 23 --sym --orbit
cadical -t 3600 -w k5-23-sym-orbit.solution k5-23-sym-orbit.cnf
python3 synthesis.py mk 30 --sym --orbit
cadical -t 3600 -w mk-30-sym-orbit.solution mk-30-sym-orbit.cnf
python3 synthesis_semantic.py k5 23 --sym --orbit --semantic --edge-active
cadical -t 1800 -w k5-23-sym-orbit-semantic-edge-active.solution k5-23-sym-orbit-semantic-edge-active.cnf
g++ -O3 -std=c++17 evolve_graph_slack.cpp -o evolve_graph_slack
./evolve_graph_slack 1800 8605
```

All long workers run at nice10. Assertions remain enabled in C++ and Python.

`synthesis_essential.py --edge-essential` adds exact minimum-circuit edge-essentiality: every nonfinal gate chooses a positive edge and the circuit forcedfalse at that gate must reject that edge. The24gate K5 star is SAT; its model satisfies every CNF clause, all32768 truth assignments, and all23 chosen forced-zero witnesses. A15gate C6 control with four globally redundant, edge-active, locally-incomparable OR gates is SAT before this new constraint and UNSAT after it. Independent full truth and forced-gate replay identify exactly four nonessential gates. These controls test the encoding; they do not prove a target lower bound. Large generated control CNFs are reproducible using `pin_gates.py` and the archived verified gate JSON; the K5 essentiality control reproduces byte-for-byte with SHA25680c9db90de8856c0fb1cd6c109586821b62d37c1c09e7c2abfa81fefd427368d.

The compact edge-essentiality block passed independent review at source SHA256af3a25897085936f07e63d584e55ee02eecce88845b90e0794382049b4953a30. Fresh independent decoder/positive/negative-control logs are `essential-review-*`. The next prepared K5-23 instance has10414 variables and245197 clauses; generate it with `python3 synthesis_essential.py k5 23 --sym --orbit --semantic --edge-active --edge-essential`. Root authorized one30minute run after the original K5 worker reaches its wall-clock cap.

Original K5-23 sym+orbit run reached its3600second wall cap with UNKNOWN/exit0 (3600.01s wall,1337.73s CPU). The reviewed stronger edge-essential run started2026-11-25T13:36:04.275826Z with1800s cap; exact argv/start/PID are in its `.run.json`, currently a running checkpoint. See SEARCH-OUTCOMES.json for completed long runs.
