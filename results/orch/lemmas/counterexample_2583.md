# Counterexample strategy for L-meta-2583

Root obtained this lease after the previous Petersen lease returned HTTP 410. All old Petersen solver processes were stopped gracefully, with complete logs and compressed incomplete proof prefixes preserved. No result was established for the previous gap.

## Exact semantics

`TopForm.IsAO2 n C` means AND/OR gates only, exactly two inputs per gate, and every input wire points backward. `ReadK.IsReadK n C 1` means that every prime implicant has one proof tree jointly using each of its variables at most once. It does not mean global input fanout one, nor independent per-variable proof trees.

The intended finite refutation route is a 26-gate AO2 circuit for the Fano incidence function. The existing read-1 lower-bound route gives 27 gates for this graph, so such a circuit would rule out a no-larger read-1 replacement. That lower bound still needs to be included and checked in the final proof; a search result alone would not establish the refutation.

## Fano data and positive controls

Use seven points and seven lines. Line l consists of points l, l+1, l+3 modulo seven. Point variables are wires 0–6; line variables are wires 7–13. Python exhaustively checked line sizes three and unique common lines for distinct point pairs.

All 16,384 input subsets were independently enumerated. There are 458 independent sets and 37 maximal independent sets. The 21 edge assignments plus those 37 maximal independent sets give 58 sufficient test rows for monotone candidates: every true input contains an edge, and every false input is contained in a maximal independent set.

The explicit 27-gate star construction passed all 16,384 truth rows, every AO2 wire-reference check, and joint read-vector (1,1) checks on all 21 edge implicants. The SAT encoder also accepted its reordered positive control and decoded a circuit correct on the full truth table.

Files under `/tmp/oec/pequalnp-pilot-99/gap2583/counterexample`:

- `fano.json`: exact incidence, maximal independent sets, and 58 test rows.
- `upper27.json`: explicit positive-control circuit and validation counts.
- `upper27-colex-fix.json`: topologically reordered witness used by the SAT control.
- `fano_sat.py`, `fano27-control.*`: encoder and complete positive-control outputs.
- `fano_search.cpp`: bit-parallel local search, with all 58 rows packed into one word.

## Active searches

After root renewed at 14:47:55 UTC, started a ten-minute 26-gate local search and a five-minute SAT probe. The local search starts from both point-star and line-star constructions, removes one gate, and explores AND/OR rewrites, wiring changes, and crossover. The SAT search requires connected gates with ordered distinct inputs and a nondecreasing maximum-fanin topological order. These are search restrictions; no UNSAT result from that restricted model is being claimed as a proof of the posted statement. Any returned model is checked independently on all 16,384 assignments.

Both searches retain exact inputs, source, complete stdout, and complete stderr. No 26-gate witness has been found yet.


## Search update 2026-11-25 14:55 UTC

- Initial 26-gate SAT probe ran five minutes and returned UNKNOWN (exit0), not UNSAT. Formula 7254 variables and149727 clauses; complete stdout/stderr retained in scratch.
- Optional edge-visible pruning adds one clause per gate requiring acceptance of some positive edge row, and excludes direct ANDs of nonincident raw-input pairs. Its fixed27 positive control returned SAT and independently passed all16384 inputs. The26 formula has151573 clauses and is running a ten-minute probe.
- The initial stochastic26 run remains one missing edge away. A separate weighted run penalizes false-negative edge rows eightfold, invisible gates, and fewer than eight ANDs; this is only a search heuristic and does not assert a lower bound on AND count.
- Bounded structural tests for a dirty first AND at canonical size returned UNSAT for paths on3,4,5,6 vertices and cycle6. Cycle8 timed out. These tests assume sorted distinct sources, all gates used, and all inputs used; they are not Lean certificates and do not prove a general clean-first-AND statement.
- Inspected L_meta_6076: its65-gate q3 construction is the64-gate star expression with its last OR-over-AND distributed to an AND root, at an extra one-gate cost. It is not evidence of a smaller nonlinear circuit.

Original stochastic26 search finished600 seconds and3986685952 mutations. Best candidate misses one minimal positive edge assignment and is wrong on47 of16384 full truth rows. It is not a counterexample.
